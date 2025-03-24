using System.Diagnostics;
using System.Net;
using System.Net.WebSockets;
using System.Reflection.Metadata.Ecma335;
using System.Reflection.PortableExecutable;
using System.Security.Cryptography;
using System.Text;
using Microsoft.Z3;
using StringBreaker.Constraints.ConstraintElement;
using StringBreaker.Constraints.Modifier;
using StringBreaker.IntUtils;
using StringBreaker.MiscUtils;
using StringBreaker.Tokens;

namespace StringBreaker.Constraints;

public enum BacktrackReasons {
    Unevaluated,
    Satisfied,
    // These are actual conflicts
    SymbolClash,
    ParikhImage,
    Subsumption,
    Arithmetic,
    SMT,
    ChildrenFailed,
    // Those are resolved by iterative deepening
    DepthLimit,
    ComplexityLimit,
    BothLimits,
}

public class NielsenNode {

    public int Id { get; }
    public NielsenGraph Graph { get; }

    public NielsenEdge? Parent { get; } // This is not necessarily the only ingoing edge [null is the unique "root"]
    public List<NielsenEdge>? Outgoing { get; set; } // Acyclic!!
    public NielsenNode? SubsumptionParent { get; set; }
    public bool UnitNode => Outgoing is not null && Outgoing.Count == 1; // There is no assumption literal in the outgoing edge
    public BacktrackReasons Reason { get; set; } = BacktrackReasons.Unevaluated;
    public bool IsConflict => IsConflictReason(Reason);
    public bool IsSatisfied => Reason == BacktrackReasons.Satisfied;
    public bool FullyExpanded => IsConflict || IsSatisfied || (Outgoing is not null && Outgoing.All(o => o.Tgt.FullyExpanded));

    public StrConstraintSet<StrEq> StrEq { get; init; } = new([]);
    public StrConstraintSet<StrNonEq> StrNEq { get; init; } = new([]);
    public IntConstraintSet<IntEq> IntEq { get; init; } = new([]);
    public IntConstraintSet<IntNonEq> IntNEq { get; init; } = new([]);
    public IntConstraintSet<IntLe> IntLe { get; init; } = new([]);
    public Dictionary<NonTermInt, Interval> IntBounds { get; init; } = []; // x \in [i, j]

    public IEnumerable<IConstraintSet> AllConstraintSets
    {
        get
        {
            yield return StrEq;
            yield return StrNEq;
            yield return IntEq;
            yield return IntNEq;
            yield return IntLe;
        }
    }

    public IEnumerable<Constraint> AllConstraints
    {
        get
        {
            foreach (var cnstrSet in AllConstraintSets) {
                foreach (var cnstr in cnstrSet.EnumerateBaseConstraints()) {
                    yield return cnstr;
                }
            }
        }
    }

    public int StrConstraintCnt => AllConstraintSets.Sum(o => o.Count);

    public IEnumerable<IStrConstraintSet> AllStrConstraintSets
    {
        get
        {
            yield return StrEq;
            yield return StrNEq;
        }
    }

    public IEnumerable<StrConstraint> AllStrConstraints
    {
        get
        {
            foreach (var cnstrSet in AllStrConstraintSets) {
                foreach (var cnstr in cnstrSet.EnumerateConstraints()) {
                    yield return cnstr;
                }
            }
        }
    }

    public IEnumerable<IIntConstraintSet> AllIntConstraintSets
    {
        get
        {
            yield return IntEq;
            yield return IntNEq;
            yield return IntLe;
        }
    }

    public IEnumerable<IntConstraint> AllIntConstraints
    {
        get
        {
            foreach (var cnstrSet in AllIntConstraintSets) {
                foreach (var cnstr in cnstrSet.EnumerateConstraints()) {
                    yield return cnstr;
                }
            }
        }
    }

    public NielsenNode(NielsenGraph graph) {
        Graph = graph;
        Id = graph.NodeCnt;
        graph.AddNode(this);
    }

    public NielsenNode(NielsenNode parent, IReadOnlyList<Subst> subst) : this(parent.Graph) {
        Debug.Assert(parent.Outgoing is not null);
        Parent = new NielsenEdge(parent,
            (BoolExpr)Graph.Ctx.MkFreshConst("P", Graph.Ctx.BoolSort), subst, this);
        if (Parent.Src.Parent is not null)
            AssertToZ3(Parent.Src.Parent.Assumption);
        parent.Outgoing.Add(Parent);

        Expr[] lhs = new Expr[subst.Count];
        for (int i = 0; i < lhs.Length; i++) {
            lhs[i] = subst[i].KeyExpr(Graph);
        }
        Parent.IncModCount(Graph);
        for (int i = 0; i < lhs.Length; i++) {
            var rhs = subst[i].ValueExpr(Graph);
            AssertToZ3(Graph.Propagator.Ctx.MkEq(lhs[i], rhs));
        }
        Parent.DecModCount(Graph);
    }

    public IEnumerable<NielsenEdge> EnumerateParents() {
        NielsenNode current = this;
        while (current.Parent is not null) {
            yield return current.Parent;
            current = current.Parent.Src;
        }
    }

    public HashSet<NielsenNode> GetParentSet() {
        HashSet<NielsenNode> parents = [];
        foreach (var parent in EnumerateParents()) {
            parents.Add(parent.Src);
        }
        return parents;
    }

    public void AssertToZ3(IEnumerable<BoolExpr> e) {
        foreach (var ex in e) {
            AssertToZ3(ex);
        }
    }

    public void AssertToZ3(BoolExpr e) {
        if (e.IsTrue)
            return;
        if (Parent is null) {
            Graph.SubSolver.Assert(e);
            return;
        }
        Graph.SubSolver.Assert(
            Graph.Ctx.MkImplies(Parent.Assumption, e));
    }

    public bool IsIntFixed(NonTermInt v, out Len val) {
        val = default;
        if (!IntBounds.TryGetValue(v, out var bounds)) 
            return false;
        val = bounds.Min;
        return bounds.IsUnit;
    }
    public bool IsBoundLower(NonTermInt v, out Len val) {
        val = default;
        if (!IntBounds.TryGetValue(v, out var bounds)) 
            return false;
        val = bounds.Min;
        return bounds.Min.IsNegInf;
    }

    public bool IsBoundUpper(NonTermInt v, out Len val) {
        val = default;
        if (!IntBounds.TryGetValue(v, out var bounds)) 
            return false;
        val = bounds.Max;
        return bounds.Max.IsPosInf;
    }

    public SimplifyResult AddExactIntBound(NonTermInt v, Len val) {
        // TODO: Check that Parikh (actually their sum) is at most Length
        if ((v is LenVar or Parikh) && val.IsNeg)
            return SimplifyResult.Conflict;
        Interval i;
        if (!IntBounds.TryGetValue(v, out var bounds)) {
            i = new Interval(val, val);
            IntBounds.Add(v, i);
            AssertToZ3(i.ToZ3Constraint(v, Graph));
            return SimplifyResult.Restart;
        }
        if (val > bounds.Max || val < bounds.Min)
            return SimplifyResult.Conflict;
        if (bounds.IsUnit)
            return SimplifyResult.Satisfied;
        i = new Interval(val, val);
        IntBounds[v] = i;
        AssertToZ3(i.ToZ3Constraint(v, Graph));
        return SimplifyResult.Restart;
    }

    public SimplifyResult AddLowerIntBound(NonTermInt v, Len val) {
        if ((v is LenVar or Parikh) && val.IsNeg)
            val = 0;
        Interval i;
        if (!IntBounds.TryGetValue(v, out var bounds)) {
            i = new Interval(val, Len.PosInf);
            IntBounds.Add(v, i);
            AssertToZ3(i.ToZ3Constraint(v, Graph));
            return SimplifyResult.Restart;
        }
        if (val > bounds.Max)
            return SimplifyResult.Conflict;
        if (val <= bounds.Min)
            return SimplifyResult.Satisfied;
        i = new Interval(val, bounds.Max);
        IntBounds[v] = i;
        AssertToZ3(i.ToZ3Constraint(v, Graph));
        return SimplifyResult.Restart;
    }

    public SimplifyResult AddHigherIntBound(NonTermInt v, Len val) {
        if ((v is LenVar or Parikh) && val.IsNeg)
            return SimplifyResult.Conflict;
        Interval i;
        if (!IntBounds.TryGetValue(v, out var bounds)) {
            i = new Interval(v is LenVar or Parikh ? 0 : Len.NegInf, val);
            IntBounds.Add(v, i);
            AssertToZ3(i.ToZ3Constraint(v, Graph));
            return SimplifyResult.Restart;
        }
        if (val < bounds.Min)
            return SimplifyResult.Conflict;
        if (val >= bounds.Max)
            return SimplifyResult.Satisfied;
        i = new Interval(bounds.Min, val);
        IntBounds[v] = i;
        AssertToZ3(i.ToZ3Constraint(v, Graph));
        return SimplifyResult.Restart;
    }

    public bool ConsistentIntVal(IntVar var, Len v) => 
        !IntBounds.TryGetValue(var, out var bounds) || bounds.Contains(v);

    // lhs == rhs
    // No need to copy anything!
    public bool IsEq(Poly lhs, Poly rhs) {
        IntEq eq = new(lhs.Clone(), rhs);
        if (IntEq.Contains(eq))
            return true;
        var bounds = eq.Poly.GetBounds(this);
        return bounds is { IsUnit: true, Min.IsZero: true };
    }

    // p == 0 || p <= 0 [for implementation syntactic reasons, p == 0 can be true and p <= 0 can be false]
    // No need to copy anything!
    public bool IsPowerElim(Poly p) => IsZero(p) || IsNonPos(p);

    // p == 0
    // No need to copy anything!
    public bool IsZero(Poly p) => IsEq(p, new Poly());

    // p == 1
    // No need to copy anything!
    public bool IsOne(Poly p) => IsEq(p, new Poly(1));

    // lhs <= rhs
    // lhs - rhs <= 0
    // No need to copy anything!
    public bool IsLe(Poly lhs, Poly rhs) {
        IntLe le = ConstraintElement.IntLe.MkLe(lhs.Clone(), rhs);
        if (IntLe.Contains(le))
            return true;
        var bounds = le.Poly.GetBounds(this);
        return bounds.Max <= 0;
    }

    // lhs < rhs
    // lhs - rhs < 0
    // lhs - rhs < 0
    // lhs - rhs + 1 <= 0
    // No need to copy anything!
    public bool IsLt(Poly lhs, Poly rhs) {
        IntLe le = ConstraintElement.IntLe.MkLt(lhs.Clone(), rhs);
        if (IntLe.Contains(le))
            return true;
        var bounds = le.Poly.GetBounds(this);
        return bounds.Max <= 0;
    }

    // p < 0
    // No need to copy anything!
    public bool IsNeg(Poly p) => IsLt(p, new Poly());

    // p <= 0
    // No need to copy anything!
    public bool IsNonPos(Poly p) => IsLe(p, new Poly());

    // p > 0
    // No need to copy anything!
    public bool IsPos(Poly p) => IsLt(new Poly(), p);

    // p >= 0
    // No need to copy anything!
    public bool IsNonNeg(Poly p) => IsLe(new Poly(), p);

    public bool Extend() {
        if (Outgoing is not null)
            return !IsConflict; // We might have already expended it (unit or iterative deepening)
        // TODO: Backtrack if nesting to high
        // get minimal split
        Debug.Assert(AllStrConstraints.Any());
        Debug.Assert(Outgoing is null);
        ModifierBase? bestModifier = null;
        foreach (var cnstr in AllStrConstraints) {
            ModifierBase currentModifier = cnstr.Extend(this);
            if (bestModifier is null || currentModifier.CompareTo(bestModifier) < 0)
                bestModifier = currentModifier;
        }
        Debug.Assert(bestModifier is not null);
        Debug.Assert(Outgoing is null);
        Outgoing = [];
        bestModifier.Apply(this);
        foreach (var child in Outgoing) {
            child.Tgt.AssertToZ3(Graph.Ctx.MkAnd(child.SideConstraints.Select(o => o.ToExpr(Graph))));
            child.IncModCount(Graph);
            Simplify(child.Tgt);
            child.DecModCount(Graph);
        }
        return true;
    }

    public static BacktrackReasons Simplify(NielsenNode node) {

        List<NielsenNode> nodeChain = [];

        void Fail() {
            for (var i = nodeChain.Count; i > 0; i--) {
                var n = nodeChain[i - 1];
                // Inherit reason for only child
                n.Reason = BacktrackReasons.ChildrenFailed;
                n.Parent!.DecModCount(node.Graph);
            }
        }

        while (true) {
            DetModifier mod = new();
            var reason = node.Simplify(mod.Substitutions, mod.SideConstraints);
            if (reason is not BacktrackReasons.Unevaluated or BacktrackReasons.Satisfied) {
                node.Reason = reason;
                Fail();
                return reason;
            }

            if (mod.Trivial) {
                if (node.Graph.AddSumbsumptionCandidate(node)) {
                    for (var i = nodeChain.Count; i > 0; i--) {
                        nodeChain[i - 1].Parent!.DecModCount(node.Graph);
                    }
                    return BacktrackReasons.Unevaluated;
                }
                node.Reason = BacktrackReasons.Subsumption;
                Fail();
                return reason;
            }
            node.Outgoing = [];
            mod.Apply(node);
            Debug.Assert(node.UnitNode);
            Debug.Assert(node.Outgoing is not null);

            if (node.Outgoing[0].SideConstraints.IsNonEmpty())
                node.Outgoing[0].Tgt.AssertToZ3(node.Graph.Ctx.MkAnd(mod.SideConstraints.Select(o => o.ToExpr(node.Graph))));

            node.Outgoing![0].IncModCount(node.Graph);
            node = node.Outgoing![0].Tgt;
            nodeChain.Add(node);
        }
    }

    public void CollectSymbols(HashSet<NamedStrToken> vars, HashSet<SymCharToken> sChars, HashSet<IntVar> iVars, HashSet<CharToken> alphabet) {
        foreach (var cnstr in AllStrConstraints) {
            cnstr.CollectSymbols(vars, sChars, iVars, alphabet);
        }
    }

    static int simplifyCnt;

    public BacktrackReasons Simplify(List<Subst> substitution, HashSet<Constraint> newSideConstraints) {
        simplifyCnt++;
        Log.WriteLine("Simplify: " + simplifyCnt);
        HashSet<Constraint> toRemove = [];
        bool restart = true;
        while (restart) {
            restart = false;
            foreach (var c1 in AllConstraints) {
                if (c1.Satisfied)
                    continue;
                BacktrackReasons reason = BacktrackReasons.Unevaluated;
                switch (c1.Simplify(this, substitution, newSideConstraints, ref reason)) {
                    case SimplifyResult.Conflict:
                        Debug.Assert(IsActualConflict(reason));
                        return reason;
                    case SimplifyResult.Satisfied:
                        toRemove.Add(c1);
                        continue;
                    case SimplifyResult.Restart:
                        // Maybe we do not need this anymore... (assertion here just to check)
                        Debug.Assert(false);
                        restart = true;
                        continue;
                    case SimplifyResult.RestartAndSatisfied:
                        restart = true;
                        toRemove.Add(c1);
                        continue;
                    case SimplifyResult.Proceed:
                        break;
                    default:
                        throw new ArgumentOutOfRangeException();
                }
            }
        }
        foreach (var c in toRemove) {
            RemoveConstraint(c);
        }
        return BacktrackReasons.Unevaluated;
    }

    public void RemoveConstraint(Constraint c) {
        foreach (var cnstrSet in AllConstraintSets) {
            if (cnstrSet.Remove(c))
                return;
        }
        Debug.Assert(false);
    }

    public NielsenNode MkChild(NielsenNode parent, IReadOnlyList<Subst> subst) {
        Debug.Assert(parent.Outgoing is not null);
        return new NielsenNode(parent, subst) {
            StrEq = StrEq.Clone(),
            StrNEq = StrNEq.Clone(),
            IntEq = IntEq.Clone(),
            IntNEq = IntNEq.Clone(),
            IntLe = IntLe.Clone(),
            IntBounds = new Dictionary<NonTermInt, Interval>(IntBounds),
        };
    }

    public override bool Equals(object? obj) {
        if (obj is not NielsenNode other)
            return false;
        return Id == other.Id && ReferenceEquals(Graph, other.Graph);
    }

    public bool EqualContent(NielsenNode other) {
        if (ReferenceEquals(this, other))
            return true;
        if (StrConstraintCnt != other.StrConstraintCnt || IntBounds.Count != other.IntBounds.Count)
            return false;
        foreach (var cnstrPair in AllConstraints.Zip(other.AllConstraints)) {
            if (!cnstrPair.First.Equals(cnstrPair.Second))
                return false;
        }
        foreach (var (v, i) in IntBounds) {
            if (!other.IntBounds.TryGetValue(v, out var i2) || i != i2)
                return false;
        }
        return true;
    }

    public override int GetHashCode() =>
        AllConstraintSets.Aggregate(164304773, (i, v) => i + 366005033 * Id);

    public void AddConstraints(IEnumerable<Constraint> cnstrs) {
        foreach (var cond in cnstrs) {
            AddConstraints(cond);
        }
    }

    public void AddConstraints(Constraint cnstr) {
        switch (cnstr) {
            case StrEq sEq:
                StrEq.Add(sEq);
                break;
            case StrNonEq sNEq:
                StrNEq.Add(sNEq);
                break;
            case IntEq iEq:
                IntEq.Add(iEq);
                break;
            case IntNonEq iNEq:
                IntNEq.Add(iNEq);
                break;
            case IntLe iLe:
                IntLe.Add(iLe);
                break;
            default:
                throw new ArgumentOutOfRangeException();
        }
    }

    // Checks if stronger is more constrained than this
    public bool Subsumes(NielsenNode stronger) {
        Debug.Assert(stronger.StrEq.Equals(StrEq));
        return EqualContent(stronger);
        //if (!BoundsSubsumes(stronger))
        //    return false;
        // TODO: Actually we might strengthen this quite a bit
        return AllConstraints.SequenceEqual(stronger.AllConstraints);
    }

#if false
    // Not sure, we need this
    bool BoundsSubsumes(NielsenNode stronger) {
        if (IntBounds.Count > stronger.IntBounds.Count)
            return false;
        foreach (var v in IntBounds) {
            if (!stronger.IntBounds.TryGetValue(v.Key, out var si))
                return false;
            if (!si.Contains(v.Value))
                return false;
        }
        return true;
    }
#endif

    public static bool IsConflictReason(BacktrackReasons reason) =>
        reason is
            BacktrackReasons.SymbolClash or
            BacktrackReasons.ParikhImage or
            BacktrackReasons.SMT or
            BacktrackReasons.Arithmetic or
            BacktrackReasons.Subsumption or
            BacktrackReasons.ChildrenFailed;

    public static bool IsResourceReason(BacktrackReasons reason) =>
        reason is
            BacktrackReasons.DepthLimit or
            BacktrackReasons.ComplexityLimit or
            BacktrackReasons.BothLimits;

    public static bool IsActualConflict(BacktrackReasons reason) =>
        IsConflictReason(reason) && reason != BacktrackReasons.ChildrenFailed;

    public static string ReasonToString(BacktrackReasons reason) => reason switch {
        BacktrackReasons.Unevaluated => "Unevaluated",
        BacktrackReasons.Satisfied => "Satisfied",
        BacktrackReasons.SymbolClash => "Symbol Clash",
        BacktrackReasons.ParikhImage => "Parikh Image",
        BacktrackReasons.Arithmetic => "Arithmetic",
        BacktrackReasons.Subsumption => "Subsumption",
        BacktrackReasons.SMT => "SMT",
        BacktrackReasons.ChildrenFailed => "Children Failed",
        BacktrackReasons.DepthLimit => "Depth Limit",
        BacktrackReasons.ComplexityLimit => "Complexity Limit",
        BacktrackReasons.BothLimits => "Depth & Complexity Limit",
        _ => throw new ArgumentOutOfRangeException()
    };

    static BacktrackReasons MergeChildrenReasons(BacktrackReasons r1, BacktrackReasons r2) {
        if (r1 == BacktrackReasons.Unevaluated || r2 == BacktrackReasons.Unevaluated)
            return BacktrackReasons.Unevaluated;
        if (r1 == BacktrackReasons.Satisfied || r2 == BacktrackReasons.Satisfied)
            return BacktrackReasons.Satisfied;
        if (IsResourceReason(r1) && IsResourceReason(r2))
            return r1 == r2 ? r1 : BacktrackReasons.BothLimits;
        if (IsResourceReason(r1))
            return r1;
        if (IsResourceReason(r2))
            return r2;
        return BacktrackReasons.ChildrenFailed;
    }

    // Unit steps are not countered for depth (or complexity) bound
    public bool Check(int dep, int comp) {
        Status res = Parent is null ? Graph.SubSolver.Check() : Graph.SubSolver.Check(Parent.Assumption);
        Debug.Assert(res != Status.UNKNOWN);
        if (res == Status.UNSATISFIABLE) {
            Reason = BacktrackReasons.SMT;
            return false;
        }

        if (!AllStrConstraints.Any()) {
            // We can also just say assumption_child => assumption_parent
            // and assume only the deepest child
            Reason = BacktrackReasons.Satisfied;
            Graph.SatNodes.Add(this);
            return true;
        }
        if (comp > Graph.ComplexityBound) {
            Reason = BacktrackReasons.ComplexityLimit;
            return false;
        }
        if (dep > Graph.DepthBound) {
            Reason = BacktrackReasons.DepthLimit;
            return false;
        }
        if (!Extend())
            return true;
        bool first = true;
        BacktrackReasons reason = Reason;
        Debug.Assert(Outgoing is not null);
        bool sat = false;
        foreach (var outgoing in Outgoing) {
            if (outgoing.Tgt is { IsConflict: false, IsSatisfied: false }) {
                outgoing.IncModCount(Graph);
                bool r = outgoing.Tgt.Check(dep + 1, comp);
                outgoing.DecModCount(Graph);
                if (r) {
                    Reason = BacktrackReasons.Satisfied;
                    sat = true;
                    if (!Options.FullGraphExpansion)
                        return true;
                    reason = MergeChildrenReasons(reason, BacktrackReasons.Satisfied);
                }
            }
            if (first) {
                reason = IsConflictReason(outgoing.Tgt.Reason) ? BacktrackReasons.ChildrenFailed : outgoing.Tgt.Reason;
                first = false;
            }
            else
                reason = MergeChildrenReasons(reason, outgoing.Tgt.Reason);
        }
        Reason = reason;
        return sat;
    }

    public override string ToString() {
        StringBuilder sb = new();
        if (AllStrConstraints.Any()) {
            sb.AppendLine("Cnstr:");
            foreach (var cnstr in AllConstraints) {
                sb.Append('\t').Append(cnstr).AppendLine();
            }
        }
        if (IntBounds.IsNonEmpty()) {
            sb.AppendLine("Bounds:");
            foreach (var (v, i) in IntBounds) {
                sb.Append('\t').Append(i.Min).Append(" \u2264 ").Append(v).Append(" \u2264 ").Append(i.Max).AppendLine();
            }
        }
        return sb.Length == 0 ? "\u22a4" : sb.ToString();
    }

    public static string DotEscapeStr(string s) =>
        s.Replace("<", "&lt;").Replace(">", "&gt;");

    public string ToHTMLString() {
        StringBuilder sb = new();
        if (AllConstraints.Any()) {
            sb.Append("Cnstr:\\n");
            foreach (var cnstr in AllConstraints) {
                sb.Append(DotEscapeStr(cnstr.ToString())).Append("\\n");
            }
        }
        if (IntBounds.IsNonEmpty()) {
            sb.Append("Bounds:\\n");
            foreach (var (v, i) in IntBounds) {
                sb.Append(i.Min).Append(" \u2264 ").Append(DotEscapeStr(v.ToString())).Append(" \u2264 ").Append(i.Max).Append("\\n");
            }
        }
        return sb.Length == 0 ? "\u22a4" : sb.ToString();
    }

    public string RootPathToDot() {
        StringBuilder sb = new();
        var relevant = GetParentSet();
        relevant.Add(this);
        sb.AppendLine("digraph G {");
        foreach (var node in relevant) {
            sb.Append("\t")
                .Append(node.Id)
                .Append(" [label=\"")
                .Append(node.Id).Append("\\n")
                .Append(node.ToHTMLString())
                .Append('"');
            if (node.IsConflict)
                sb.Append(", color=red");
            sb.AppendLine("];");
        }
        foreach (var node in relevant) {
            foreach (var edge in node.Outgoing ?? []) {
                if (!relevant.Contains(edge.Tgt))
                    continue;
                sb.Append("\t")
                    .Append(node.Id)
                    .Append(" -> ")
                    .Append(edge.Tgt.Id)
                    .Append(" [label=\"")
                    .Append(DotEscapeStr(edge.ModStr))
                    .AppendLine("\"];");
            }
        }
        sb.AppendLine("}");
        return sb.ToString();
    }
}