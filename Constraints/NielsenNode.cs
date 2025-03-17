using System.Diagnostics;
using System.Numerics;
using System.Text;
using System.Xml.Linq;
using Microsoft.Z3;
using StringBreaker.Constraints.ConstraintElement;
using StringBreaker.Constraints.Modifier;
using StringBreaker.IntUtils;
using StringBreaker.MiscUtils;
using StringBreaker.Tokens;

namespace StringBreaker.Constraints;

public class NielsenNode {

    public int Id { get; }
    public NielsenGraph Graph { get; }

    public NielsenEdge? Parent { get; } // This is not necessarily the only ingoing edge [null is the unique "root"]
    public List<NielsenEdge>? Outgoing { get; set; } // Acyclic!!
    public bool UnitNode => Outgoing is not null && Outgoing.Count == 1; // There is no assumption literal in the outgoing edge
    public bool IsConflict { get; set; } // For failure caching

    public StrConstraintSet<StrEq> StrEq { get; init; } = new([]);
    public IntConstraintSet<IntEq> IntEq { get; init; } = new([]);
    public IntConstraintSet<IntLe> IntLe { get; init; } = new([]);
    public Dictionary<NonTermInt, Interval> IntBounds { get; init; } = []; // x \in [i, j]

    public IEnumerable<IConstraintSet> AllConstraintSets
    {
        get
        {
            yield return StrEq;
            yield return IntEq;
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

    public NielsenNode(NielsenGraph graph, NielsenNode parent, IReadOnlyList<Subst> subst) : this(graph) {
        Debug.Assert(parent.Outgoing is not null);
        Parent = new NielsenEdge(parent,
            (BoolExpr)Graph.Ctx.MkFreshConst("P", Graph.Ctx.BoolSort), subst, this);
        if (Parent.Src.Parent is not null)
            Graph.SubSolver.Assert(Graph.Ctx.MkImplies(Parent.Assumption, Parent.Src.Parent.Assumption));
        parent.Outgoing.Add(Parent);
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
        if (v is LenVar && val.IsNeg)
            return SimplifyResult.Conflict;
        if (!IntBounds.TryGetValue(v, out var bounds)) {
            IntBounds.Add(v, new Interval(val, val));
            return SimplifyResult.Restart;
        }
        if (val > bounds.Max || val < bounds.Min)
            return SimplifyResult.Conflict;
        if (bounds.IsUnit)
            return SimplifyResult.Satisfied;
        IntBounds[v] = new Interval(val, val);
        return SimplifyResult.Restart;
    }

    public SimplifyResult AddLowerIntBound(NonTermInt v, Len val) {
        if (v is LenVar && val.IsNeg)
            val = 0;
        if (!IntBounds.TryGetValue(v, out var bounds)) {
            IntBounds.Add(v, new Interval(val, Len.PosInf));
            return SimplifyResult.Restart;
        }
        if (val > bounds.Max)
            return SimplifyResult.Conflict;
        if (val <= bounds.Min)
            return SimplifyResult.Satisfied;
        IntBounds[v] = new Interval(val, bounds.Max);
        return SimplifyResult.Restart;
    }

    public SimplifyResult AddHigherIntBound(NonTermInt v, Len val) {
        if (v is LenVar && val.IsNeg)
            return SimplifyResult.Conflict;
        if (!IntBounds.TryGetValue(v, out var bounds)) {
            IntBounds.Add(v, new Interval(v is LenVar ? 0 : Len.NegInf, val));
            return SimplifyResult.Restart;
        }
        if (val < bounds.Min)
            return SimplifyResult.Conflict;
        if (val >= bounds.Max)
            return SimplifyResult.Satisfied;
        IntBounds[v] = new Interval(bounds.Min, val);
        return SimplifyResult.Restart;
    }

    public bool ConsistentIntVal(IntVar var, Len v) => 
        !IntBounds.TryGetValue(var, out var bounds) || bounds.Contains(v);

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
        bool inconsistent = true;
        foreach (var child in Outgoing) {
            Graph.SubSolver.Assert(Graph.Ctx.MkImplies(child.Assumption,
                Graph.Ctx.MkAnd(child.SideConstraints.Select(o => o.ToExpr(Graph)))));
            if (!Simplify(child.Tgt))
                Debug.Assert(child.Tgt.IsConflict);
            else
                inconsistent = false;
        }
        IsConflict = inconsistent;
        return !inconsistent;
    }

    public static bool Simplify(NielsenNode node) {
        List<NielsenNode> nodeChain = [];
        while (true) {
            nodeChain.Add(node);
            DetModifier mod = new();
            if (!node.Simplify(mod.Substitutions, mod.SideConstraints)) {
                foreach (var n in nodeChain) {
                    n.IsConflict = true;
                }
                return false;
            }
            if (mod.Trivial)
                return true;
            node.Outgoing = [];
            mod.Apply(node);
            Debug.Assert(node.UnitNode);
            node = node.Outgoing![0].Tgt;
        }
    }

    void CollectSymbols(HashSet<StrVarToken> vars, HashSet<CharToken> alphabet) {
        foreach (var cnstr in AllStrConstraints) {
            cnstr.CollectSymbols(vars, alphabet);
        }
    }

    static int simplifyCnt;

    public bool Simplify(List<Subst> substitution, HashSet<Constraint> newSideConstraints) {
        simplifyCnt++;
        Log.WriteLine("Simplify: " + simplifyCnt);
        HashSet<Constraint> toRemove = [];
        bool restart = true;
        while (restart) {
            restart = false;
            foreach (var c1 in AllConstraints) {
                if (restart)
                    break;
                if (c1.Satisfied)
                    continue;
                switch (c1.Simplify(this, substitution, newSideConstraints)) {
                    case SimplifyResult.Conflict:
                        return false;
                    case SimplifyResult.Satisfied:
                        toRemove.Add(c1);
                        continue;
                    case SimplifyResult.Restart:
                        restart = true;
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
        return true;
    }

    void RemoveConstraint(Constraint c) {
        foreach (var cnstrSet in AllConstraintSets) {
            if (cnstrSet.Remove(c))
                return;
        }
        Debug.Assert(false);
    }

    public NielsenNode MkChild(NielsenNode parent, IReadOnlyList<Subst> subst) {
        Debug.Assert(parent.Outgoing is not null);
        return new NielsenNode(Graph, parent, subst) {
            StrEq = StrEq.Clone(),
            IntEq = IntEq.Clone(),
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
            case IntEq iEq:
                IntEq.Add(iEq);
                break;
            case IntLe iLe:
                IntLe.Add(iLe);
                break;
            default:
                throw new ArgumentOutOfRangeException();
        }
    }

    public SimplifyResult Check() {
        Graph.Current = this;
        if (!AllStrConstraints.Any()) {
            // We can also just say assumption_child => assumption_parent
            // and assume only the deepest child
            Status res = Parent is null ? Graph.SubSolver.Check() : Graph.SubSolver.Check(Parent.Assumption);
            Debug.Assert(res != Status.UNKNOWN);
            return res == Status.UNSATISFIABLE ? SimplifyResult.Conflict : SimplifyResult.Satisfied;
        }
        if (!Extend())
            return SimplifyResult.Conflict;
        Debug.Assert(Outgoing is not null);
        foreach (var outgoing in Outgoing) {
            if (outgoing.Tgt.IsConflict)
                continue;
            if (outgoing.Tgt.Check() == SimplifyResult.Satisfied)
                return SimplifyResult.Satisfied;
            Graph.Current = this;
        }
        return SimplifyResult.Conflict;
    }

    public override string ToString() {
        StringBuilder sb = new();
        if (AllStrConstraints.Any()) {
            sb.AppendLine("Cnstr:");
            foreach (var cnstr in AllConstraints) {
                sb.Append('\t').Append(cnstr).AppendLine();
            }
        }
        if (IntBounds.NonEmpty()) {
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
        if (AllStrConstraints.Any()) {
            sb.Append("Cnstr:\\n");
            foreach (var cnstr in AllConstraints) {
                sb.Append(DotEscapeStr(cnstr.ToString())).Append("\\n");
            }
        }
        if (IntBounds.NonEmpty()) {
            sb.Append("Bounds:\\n");
            foreach (var (v, i) in IntBounds) {
                sb.Append(i.Min).Append(" <= ").Append(DotEscapeStr(v.ToString())).Append(" <= ").Append(i.Max).Append("\\n");
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