using System.Diagnostics;
using System.Net;
using System.Net.WebSockets;
using System.Reflection.Metadata.Ecma335;
using System.Reflection.PortableExecutable;
using System.Security.Cryptography;
using System.Text;
using System.Xml.Linq;
using Microsoft.Z3;
using StringBreaker.Constraints.ConstraintElement;
using StringBreaker.Constraints.ConstraintElement.AuxConstraints;
using StringBreaker.Constraints.Modifier;
using StringBreaker.IntUtils;
using StringBreaker.MiscUtils;
using StringBreaker.Tokens;
using StringBreaker.Tokens.AuxTokens;

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
    // Resolved by iterative deepening
    DepthLimit,
}

public class NielsenNode {

    public int Id { get; }
    public NielsenGraph Graph { get; }

    public NielsenEdge? Parent { get; } // This is not necessarily the only ingoing edge [null is the unique "root"]
    public List<NielsenEdge> Outgoing { get; } = [];
    public NielsenNode? SubsumptionParent { get; set; }
    public int NonConflictingChildren { get; set; } = -1;
    public bool IsUnit => NonConflictingChildren == 1;
    public bool IsConflict => NonConflictingChildren == 0;
    public bool IsSatisfied => Reason == BacktrackReasons.Satisfied;
    public BacktrackReasons Reason { get; set; } = BacktrackReasons.Unevaluated;
    public bool FullyExpanded => IsConflict || IsSatisfied || Outgoing.All(o => o.Tgt.FullyExpanded);
    public bool IsExtended => NonConflictingChildren >= 0;

    public NList<StrEq> StrEq { get; init; } = [];
    public NList<IntEq> IntEq { get; init; } = [];
    public NList<IntLe> IntLe { get; init; } = [];

    // e.g., o \notin { a, b, p }
    public Dictionary<SymCharToken, HashSet<UnitToken>> DisEq { get; init; } = [];

    // A node is marked as progress if either
    // 1) it is root
    // 2) it results from a node by adding some eliminating substitution (e.g., x / y or x / "" or x / a^n)
    // 3) it results from a node by adding a strong side constraint (e.g., n = 0 or splitting some equation)
    // We only check progress nodes and potentially satisfied nodes by a call to Z3
    public bool IsProgressNode { get; }

    // x \in [i, j] with i, j const
    public Dictionary<NonTermInt, Interval> IntBounds { get; init; } = [];

    // Bounds for e.g., |x| might change when substituting x - we associate x with relevant integer variables depending on it
    public Dictionary<NamedStrToken, HashSet<NonTermInt>> VarBoundWatcher { get; init; } = [];

    // x... = uy... and u ground
    // If multiple x... = vy... then we keep one of them (preferably the shorter one)
    // We just cache it, as both simplify and splitting need this (no need to clone)
    public readonly Dictionary<NamedStrToken, Dictionary<NamedStrToken, Str>> forwardVarDep = []; // x... = uy... => (x, y) -> u 
    public readonly Dictionary<NamedStrToken, Dictionary<NamedStrToken, Str>> backwardVarDep = []; // ...x = ...yu => (x, y) -> u 

    public IEnumerable<Constraint> AllConstraints =>
        StrEq.OfType<Constraint>().Concat(IntEq).Concat(IntLe);

    public NielsenNode(NielsenGraph graph) {
        Graph = graph;
        Id = graph.NodeCnt;
        IsProgressNode = true;
        graph.AddNode(this);
    }

    public NielsenNode(NielsenNode parent, IReadOnlyList<Subst> subst, bool isProgress) : this(parent.Graph) {
        IsProgressNode = isProgress;
        Parent = new NielsenEdge(parent,
            (BoolExpr)Graph.Ctx.MkFreshConst("P", Graph.Ctx.BoolSort), subst, this);
        if (Parent.Src.Parent is not null)
            AssertToZ3(Parent.Src.Parent.Assumption);
        parent.Outgoing.Add(Parent);

        // Equate the lengths
        IntExpr[] lhs = new IntExpr[subst.Count];
        for (int i = 0; i < lhs.Length; i++) {
            lhs[i] = subst[i].KeyLenExpr(Graph);
        }
        int modCnt = Graph.ModCnt;
        Parent.IncModCount(Graph);
        for (int i = 0; i < lhs.Length; i++) {
            var rhs = subst[i].ValueLenExpr(Graph);
            if (!lhs[i].Equals(rhs))
                AssertToZ3(Graph.OuterPropagator.Ctx.MkEq(lhs[i], rhs));
        }
        Parent.DecModCount(Graph);
        Debug.Assert(Graph.ModCnt == modCnt);
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

    public void Apply(Subst subst) {
        foreach (var cnstr in AllConstraints) {
            cnstr.Apply(subst);
        }
        if (subst is not SubstVar v || !VarBoundWatcher.TryGetValue(v.Var, out var watch)) 
            return;
        foreach (var watched in watch) {
            var bound = IntBounds[watched];
            IntBounds.Remove(watched);
            var n = watched.Apply(subst);
            if (bound.HasLow)
                AddConstraints(ConstraintElement.IntLe.MkLe(new Poly(bound.Min), n.Clone()));
            else if (bound.HasHigh)
                AddConstraints(ConstraintElement.IntLe.MkLe(new Poly(watched), n.Clone()));
        }
        VarBoundWatcher.Remove(v.Var);
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

    void WatchVarBound(NonTermInt v) {
        HashSet<NamedStrToken> vars = [];
        v.CollectSymbols(vars, [], [], []);
        foreach (var var in vars) {
            if (!VarBoundWatcher.TryGetValue(var, out var watched))
                VarBoundWatcher.Add(var, watched = []);
            watched.Add(v);
        }
    }

    public SimplifyResult AddLowerIntBound(NonTermInt v, Len val) {
        Debug.Assert(val != Len.PosInf);
        val = Len.Max(val, v.MinLen);
        Interval i;
        if (val == v.MinLen)
            // Not very helpful
            return SimplifyResult.Proceed;
        if (!IntBounds.TryGetValue(v, out var bounds)) {
            WatchVarBound(v);
            i = new Interval(val, Len.PosInf);
            IntBounds.Add(v, i);
            AssertToZ3(i.ToZ3Constraint(v, Graph));
            return SimplifyResult.Restart;
        }
        if (val > bounds.Max)
            return SimplifyResult.Conflict;
        if (val <= bounds.Min)
            return SimplifyResult.Proceed;
        i = new Interval(val, bounds.Max);
        IntBounds[v] = i;
        AssertToZ3(i.ToZ3Constraint(v, Graph));
        return SimplifyResult.Restart;
    }

    public SimplifyResult AddHigherIntBound(NonTermInt v, Len val) {
        Debug.Assert(val != Len.NegInf);
        if (val < v.MinLen)
            return SimplifyResult.Conflict;
        if (val.IsPosInf)
            // Not very helpful
            return SimplifyResult.Proceed;
        Interval i;
        if (!IntBounds.TryGetValue(v, out var bounds)) {
            WatchVarBound(v);
            i = new Interval(v is LenVar or Parikh ? 0 : Len.NegInf, val);
            IntBounds.Add(v, i);
            AssertToZ3(i.ToZ3Constraint(v, Graph));
            return SimplifyResult.Restart;
        }
        if (val < bounds.Min)
            return SimplifyResult.Conflict;
        if (val >= bounds.Max)
            return SimplifyResult.Proceed;
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
        return eq.Simplify(this) switch {
            SimplifyResult.Satisfied => true,
            SimplifyResult.Conflict => false,
            _ => IntEq.Contains(eq),
        };
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
        return le.Simplify(this) switch {
            SimplifyResult.Satisfied => true,
            SimplifyResult.Conflict => false,
            _ => IntLe.Contains(le),
        };
    }

    // lhs < rhs
    // lhs - rhs < 0
    // lhs - rhs < 0
    // lhs - rhs + 1 <= 0
    // No need to copy anything!
    public bool IsLt(Poly lhs, Poly rhs) {
        IntLe le = ConstraintElement.IntLe.MkLt(lhs.Clone(), rhs);
        return le.Simplify(this) switch {
            SimplifyResult.Satisfied => true,
            SimplifyResult.Conflict => false,
            _ => IntLe.Contains(le),
        };
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

    public bool AreDiseq(UnitToken u1, UnitToken u2) {
        SymCharToken s;
        if (u1 is CharToken c1) {
            if (u2 is CharToken c2)
                return !c1.Equals(c2);
            s = (SymCharToken)u2;
        }
        else
            s = (SymCharToken)u1;
        return DisEq.TryGetValue(s, out var disEqs) && disEqs.Contains(u1);
    }

    public void Extend() {
        // TODO: Backtrack if nesting to high
        // get minimal split
        Debug.Assert(StrEq.Any());
        Debug.Assert(!IsExtended);
        ModifierBase? bestModifier = null;
        foreach (var cnstr in StrEq) {
            ModifierBase currentModifier = cnstr.Extend(this);
            if (bestModifier is null || currentModifier.CompareTo(bestModifier) < 0)
                bestModifier = currentModifier;
        }
        Debug.Assert(bestModifier is not null);
        bestModifier.Apply(this);
        NonConflictingChildren = 0;
        foreach (var child in Outgoing) {
            child.Tgt.AssertToZ3(Graph.Ctx.MkAnd(child.SideConstraints.Select(o => o.ToExpr(Graph))));
            int modCnt = Graph.ModCnt;
            child.IncModCount(Graph);
            SimplifyAndInit(child.Tgt);
            child.DecModCount(Graph);
            Debug.Assert(modCnt == Graph.ModCnt);
            if (!child.Tgt.IsConflict)
                NonConflictingChildren++;
        }
    }

    static int simplifyChainCnt;

    public static BacktrackReasons SimplifyAndInit(NielsenNode node) {

        List<NielsenNode> nodeChain = [node];
        simplifyChainCnt++;

        void Fail() {
            for (var i = nodeChain.Count - 1; i > 0; i--) {
                // Inherit reason for only child
                nodeChain[i - 1].Reason = BacktrackReasons.ChildrenFailed;
                nodeChain[i - 1].NonConflictingChildren = 0;
                nodeChain[i].Parent!.DecModCount(node.Graph);
            }
        }

        bool failedBefore = false;

        while (true) {
            if (node.Graph.OuterPropagator.Cancel)
                throw new SolverTimeoutException();

            DetModifier sConstr = new();
            var reason = node.Simplify(sConstr);
            if (reason is not BacktrackReasons.Unevaluated or BacktrackReasons.Satisfied) {
                node.NonConflictingChildren = 0;
                node.Reason = reason;
                Fail();
                return reason;
            }

            if (sConstr.Trivial/* || failedBefore*/) {
                // failed does not work, as a^n ... = b... could imply that n = 0
                // but another integer constraint might simplify later to n = 0, so it would fail even though it did not fail
                // Debug.Assert(sConstr.Trivial || !failedBefore); // To avoid divergence in case of bugs - still this should better not happen (e.g., add n = 0 twice after each other)
                if (node.Graph.AddSumbsumptionCandidate(node)) {
                    for (var i = nodeChain.Count - 1; i > 0; i--) {
                        nodeChain[i].Parent!.DecModCount(node.Graph);
                    }
                    return BacktrackReasons.Unevaluated;
                }
                node.Reason = BacktrackReasons.Subsumption;
                node.NonConflictingChildren = 0;
                Fail();
                return reason;
            }
            sConstr.Apply(node);
            node.NonConflictingChildren = 1;
            failedBefore = !sConstr.Success;
            Debug.Assert(node.IsUnit);
            Debug.Assert(node.Outgoing.Count == 1);

            if (node.Outgoing[0].SideConstraints.IsNonEmpty())
                node.Outgoing[0].Tgt.AssertToZ3(node.Graph.Ctx.MkAnd(sConstr.SideConstraints.Select(o => o.ToExpr(node.Graph))));

            node.Outgoing[0].IncModCount(node.Graph);
            node = node.Outgoing[0].Tgt;
            nodeChain.Add(node);
        }
    }

    public void CollectSymbols(HashSet<NamedStrToken> vars, HashSet<SymCharToken> sChars, HashSet<IntVar> iVars, HashSet<CharToken> alphabet) {
        foreach (var cnstr in StrEq) {
            cnstr.CollectSymbols(vars, sChars, iVars, alphabet);
        }
    }

    static int simplifyCnt;

    public BacktrackReasons Simplify(DetModifier sConstr) {
        simplifyCnt++;
        Log.WriteLine("Simplify: " + simplifyCnt);
        bool restart = true;
        HashSet<Constraint> toRemove = [];
        // Stuff like { 1 + y = x, 1 + x = y } or { 1 + y <= x, 1 + x <= y } will cause divergence on bounds propagation...
        // So let's ignore them unless some string equation has progress (in the end, the SMT solver has to detect unsat)
        HashSet<IntConstraint> ignored = [];
        while (restart) {
            restart = false;
            foreach (var c in AllConstraints) {
                if (c.Satisfied)
                    continue;
                BacktrackReasons reason = BacktrackReasons.Unevaluated;
                switch (c.SimplifyAndPropagate(this, sConstr, ref reason)) {
                    case SimplifyResult.Conflict:
                        Debug.Assert(IsActualConflict(reason));
                        return reason;
                    case SimplifyResult.Satisfied:
                        toRemove.Add(c);
                        continue;
                    case SimplifyResult.Restart:
                        // Maybe we do not need this anymore... (assertion here just to check)
                        if (c is IntConstraint ic && ignored.Add(ic))
                            restart = true;
                        else if (c is StrEq) 
                            ignored.Clear();
                        continue;
                    case SimplifyResult.RestartAndSatisfied:
                        restart = true;
                        toRemove.Add(c);
                        continue;
                    case SimplifyResult.Proceed:
                        break;
                    default:
                        throw new ArgumentOutOfRangeException();
                }
            }
            if (!sConstr.Trivial)
                // Better we integrate the new information 
                // otw., x...x = cxa...axc could give x / cx and x / xc but this "c" might be the same one
                // so either try to unify the substitutions, or just apply every substitution as soon as we get it
                break;
        }

        foreach (var eq in StrEq) {
            if (eq.Satisfied)
                continue;
            eq.GetNielsenDep(forwardVarDep, true);
            eq.GetNielsenDep(backwardVarDep, false);
        }
        foreach (var eq in StrEq) {
            if (eq.Satisfied)
                continue;
            eq.SimplifyUnitNielsen(sConstr, forwardVarDep, true);
            eq.SimplifyUnitNielsen(sConstr, backwardVarDep, false);
        }
        Normalize();
        foreach (var c in toRemove) {
            RemoveConstraint(c);
        }
        return BacktrackReasons.Unevaluated;
    }

    void Normalize() {
        StrEq.Sort();
        IntEq.Sort();
        IntLe.Sort();
    }

    public void RemoveConstraint(Constraint cnstr) {
        switch (cnstr) {
            case StrEq sEq:
                RemoveStrEq(sEq);
                break;
            case IntEq iEq:
                RemoveIntEq(iEq);
                break;
            case IntLe iLe:
                RemoveIntLe(iLe);
                break;
            default:
                throw new NotSupportedException();
        }
    }

    public void RemoveStrEq(StrEq toRemove) {
        // The set can contain the same element multiple times after simplification (unfortunately)
        bool succ = StrEq.Remove(toRemove);
        Debug.Assert(succ);
        while (StrEq.Remove(toRemove)) {}
    }

    public void RemoveIntEq(IntEq toRemove) {
        bool succ = IntEq.Remove(toRemove);
        Debug.Assert(succ);
        while (IntEq.Remove(toRemove)) {}
    }

    public void RemoveIntLe(IntLe toRemove) {
        bool succ = IntLe.Remove(toRemove);
        Debug.Assert(succ);
        while (IntLe.Remove(toRemove)) {}
    }

    public NielsenNode MkChild(NielsenNode parent, IReadOnlyList<Subst> subst, bool progress) {
        return new NielsenNode(parent, subst, progress) {
            StrEq = StrEq.Select(o => o.Clone()).ToNList(),
            IntEq = IntEq.Select(o => o.Clone()).ToNList(),
            IntLe = IntLe.Select(o => o.Clone()).ToNList(),
            IntBounds = new Dictionary<NonTermInt, Interval>(IntBounds),
            VarBoundWatcher = VarBoundWatcher.ToDictionary(o => o.Key, o => o.Value.ToHashSet()),
            DisEq = DisEq.ToDictionary(o => o.Key, o => o.Value.ToHashSet()),
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
        if (StrEq.Count != other.StrEq.Count || IntBounds.Count != other.IntBounds.Count || DisEq.Count != other.DisEq.Count)
            return false;
        foreach (var cnstrPair in AllConstraints.Zip(other.AllConstraints)) {
            if (!cnstrPair.First.Equals(cnstrPair.Second))
                return false;
        }
        foreach (var (v, i) in IntBounds) {
            if (!other.IntBounds.TryGetValue(v, out var i2) || i != i2)
                return false;
        }
        foreach (var (v, d1) in DisEq) {
            if (!other.DisEq.TryGetValue(v, out var d2))
                return false;
            if (d1.Count != d2.Count)
                return false;
            if (d1.Any(u => !d2.Contains(u)))
                return false;
            
        }
        return true;
    }

    // We deliberately only check for the constraints and not the bounds/diseqs (we can do this later on the semantic check)
    // This function is not in sync with Equals(object?), but this is not super important!!
    public override int GetHashCode() =>
        AllConstraints.Aggregate(164304773, (i, v) => i + 366005033 * Id);

    public void AddConstraints(IEnumerable<Constraint> cnstrs) {
        foreach (var cond in cnstrs) {
            AddConstraints(cond);
        }
    }

    public bool AddConstraints(Constraint cnstr) {
        switch (cnstr) {
            case StrEq sEq:
                return StrEq.Add(sEq);
            case IntEq iEq:
                return IntEq.Add(iEq);
            case IntLe iLe:
                return IntLe.Add(iLe);
            default:
                throw new NotSupportedException();
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
            BacktrackReasons.DepthLimit;

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
        _ => throw new ArgumentOutOfRangeException()
    };

    static BacktrackReasons MergeChildrenReasons(BacktrackReasons r1, BacktrackReasons r2) {
        if (r1 == BacktrackReasons.Unevaluated || r2 == BacktrackReasons.Unevaluated)
            return BacktrackReasons.Unevaluated;
        if (r1 == BacktrackReasons.Satisfied || r2 == BacktrackReasons.Satisfied)
            return BacktrackReasons.Satisfied;
        if (IsResourceReason(r1))
            return r1;
        if (IsResourceReason(r2))
            return r2;
        return BacktrackReasons.ChildrenFailed;
    }

    // Unit and progression steps are not countered for depth bound
    public bool Check(int dep) {
        if (!IsExtended) {
            Status z3Res = Status.UNKNOWN;
            if (IsProgressNode) {
                // We made progress - let's check if this is already enough to get an integer conflict
                // This can be expensive, so we only do this in case the formula simplified "strongly" before
                // => we ask Z3
                z3Res = Parent is null ? Graph.SubSolver.Check() : Graph.SubSolver.Check(Parent.Assumption);
                if (z3Res == Status.UNKNOWN) {
                    if (Graph.SubSolver.ReasonUnknown is "timeout" or "canceled")
                        throw new SolverTimeoutException();
                    throw new Exception("Z3 returned unknown");
                }

                if (z3Res == Status.UNSATISFIABLE) {
                    Reason = BacktrackReasons.SMT;
                    NonConflictingChildren = 0;
                    return false;
                }
            }

            if (StrEq.Count == 0) {
                // We might have already checked this if it was a progress node
                // We need a Z3 result so let's ask if we haven't already
                if (z3Res == Status.UNKNOWN) {
                    Debug.Assert(!IsProgressNode);
                    z3Res = Parent is null ? Graph.SubSolver.Check() : Graph.SubSolver.Check(Parent.Assumption);
                }
                if (z3Res == Status.UNKNOWN) {
                    if (Graph.SubSolver.ReasonUnknown is "timeout" or "canceled")
                        throw new SolverTimeoutException();
                    throw new Exception("Z3 returned unknown");
                }
                // If Z3 says unsat, we backtrack
                if (z3Res == Status.UNSATISFIABLE) {
                    Reason = BacktrackReasons.SMT;
                    return false;
                }
                // Otw. we found a candidate model
                Reason = BacktrackReasons.Satisfied;
                Graph.SatNodes.Add(this);
                return true;
            }
            if (dep > Graph.DepthBound) {
                Reason = BacktrackReasons.DepthLimit;
                return false;
            }
            Extend();
        }
        bool first = true;
        BacktrackReasons reason = Reason;
        Debug.Assert(IsExtended);
        bool sat = false;
        bool wasUnit = false; //IsUnit;
        foreach (var outgoing in Outgoing) {
            if (outgoing.Tgt is { IsConflict: false, IsSatisfied: false }) {
                outgoing.IncModCount(Graph);
                int modCnt = Graph.ModCnt;
                // we want to go deep fast if there is no danger of divergence
                int nextDep = wasUnit || outgoing.Tgt.IsProgressNode ? dep : dep + 1;
                bool r = outgoing.Tgt.Check(nextDep);
                Debug.Assert(modCnt == Graph.ModCnt);
                outgoing.DecModCount(Graph);
                if (r) {
                    Reason = BacktrackReasons.Satisfied;
                    sat = true;
                    if (!Options.FullGraphExpansion)
                        return true;
                    reason = MergeChildrenReasons(reason, BacktrackReasons.Satisfied);
                }
                else if (outgoing.Tgt.IsConflict) {
                    Debug.Assert(NonConflictingChildren > 0);
                    NonConflictingChildren--;
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
        if (StrEq.Count > 0) {
            sb.AppendLine("Cnstr:");
            foreach (var cnstr in AllConstraints) {
                sb.Append('\t').AppendLine(cnstr.ToString());
            }
        }
        if (IntBounds.IsNonEmpty()) {
            sb.AppendLine("Bounds:");
            foreach (var (v, i) in IntBounds) {
                sb.Append('\t').Append(i.Min).Append(" \u2264 ").Append(v).Append(" \u2264 ").AppendLine(i.Max.ToString());
            }
        }
        if (DisEq.IsNonEmpty()) {
            sb.AppendLine("DisEqs:");
            foreach (var (v, deq) in DisEq) {
                sb.Append('\t').Append(v).Append(" \u2209 { ").Append(string.Join(", ", deq)).AppendLine(" }");
            }
        }
        return sb.Length == 0 ? "\u22a4" : sb.ToString();
    }

    public static string DotEscapeStr(string s) =>
        s.Replace("<", "&lt;").Replace(">", "&gt;");

    public string ToHtmlString() {
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
                .Append(node.ToHtmlString())
                .Append('"');
            if (node.IsConflict)
                sb.Append(", color=red");
            sb.AppendLine("];");
        }
        foreach (var node in relevant) {
            foreach (var edge in node.Outgoing) {
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