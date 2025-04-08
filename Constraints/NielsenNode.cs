using System.Diagnostics;
using System.Text;
using Microsoft.Z3;
using StringBreaker.Constraints.ConstraintElement;
using StringBreaker.Constraints.Modifier;
using StringBreaker.IntUtils;
using StringBreaker.MiscUtils;
using StringBreaker.Strings;
using StringBreaker.Strings.Tokens;

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
    public bool Extended => Outgoing is not null;

    public StrConstraintSet<StrEq> StrEq { get; init; } = new([]);
    public IntConstraintSet<IntEq> IntEq { get; init; } = new([]);
    public IntConstraintSet<IntNonEq> IntNEq { get; init; } = new([]);
    public IntConstraintSet<IntLe> IntLe { get; init; } = new([]);

    // A node is marked as progress if either
    // 1) it is root
    // 2) it results from a node by adding some eliminating substitution (e.g., x / y or x / "" or x / a^n)
    // 3) it results from a node by adding a strong side constraint (e.g., n = 0 or splitting some equation)
    // We only check progress nodes and potentially satisfied nodes by a call to Z3
    public bool ProgressNode { get; }

    // x \in [i, j] with i, j const
    public Dictionary<NonTermInt, Interval> IntBounds { get; init; } = [];

    // Bounds for e.g., |x| might change when substituting x - we associate x with relevant integer variables depending on it
    public Dictionary<NamedStrToken, HashSet<NonTermInt>> VarBoundWatcher { get; init; } = [];

    // e.g., o \notin { a, b, p }
    public Dictionary<SymCharToken, HashSet<UnitToken>> DisEq { get; init; } = [];

    public IEnumerable<IConstraintSet> AllConstraintSets
    {
        get
        {
            yield return StrEq;
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
        ProgressNode = true;
        graph.AddNode(this);
    }

    public NielsenNode(NielsenContext ctx, IReadOnlyList<Subst> subst, bool progress) : this(ctx.Graph) {
        Debug.Assert(ctx.CurrentNode.Outgoing is not null);
        ProgressNode = progress;
        Parent = new NielsenEdge(ctx.CurrentNode,
            (BoolExpr)Graph.Ctx.MkFreshConst("P", Graph.Ctx.BoolSort), subst, this);
        if (Parent.Src.Parent is not null)
            AssertToZ3(Parent.Src.Parent.Assumption);
        ctx.CurrentNode.Outgoing.Add(Parent);

        // Equate the lengths
        IntExpr[] lhs = new IntExpr[subst.Count];
        for (int i = 0; i < lhs.Length; i++) {
            lhs[i] = subst[i].KeyLenExpr(ctx);
        }
        int modCnt = Graph.ModCnt;
        Parent.IncModCount(Graph);
        for (int i = 0; i < lhs.Length; i++) {
            var rhs = subst[i].ValueLenExpr(ctx);
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
        if (subst is not SubstVar v || !VarBoundWatcher.TryGetValue(v.VarToken, out var watch)) 
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
        VarBoundWatcher.Remove(v.VarToken);
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

    public SimplifyResult AddExactIntBound(NonTermInt v, Len val) {
        // TODO: Check that Parikh (actually their sum) is at most Length
        if (val < v.MinLen)
            return SimplifyResult.Conflict;
        Interval i;
        if (!IntBounds.TryGetValue(v, out var bounds)) {
            WatchVarBound(v);
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
        val = Len.Max(val, v.MinLen);
        Interval i;
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
            return SimplifyResult.Satisfied;
        i = new Interval(val, bounds.Max);
        IntBounds[v] = i;
        AssertToZ3(i.ToZ3Constraint(v, Graph));
        return SimplifyResult.Restart;
    }

    public SimplifyResult AddHigherIntBound(NonTermInt v, Len val) {
        if (val < v.MinLen)
            return SimplifyResult.Conflict;
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

    public void Extend(NielsenContext ctx) {
        // TODO: Backtrack if nesting to high
        // get minimal split
        Debug.Assert(AllStrConstraints.Any());
        Debug.Assert(Outgoing is null);
        ModifierBase? bestModifier = null;
        foreach (var cnstr in AllStrConstraints) {
            ModifierBase currentModifier = cnstr.Extend(ctx);
            if (bestModifier is null || currentModifier.CompareTo(bestModifier) < 0)
                bestModifier = currentModifier;
        }
        Debug.Assert(bestModifier is not null);
        Debug.Assert(Outgoing is null);
        Outgoing = [];
        bestModifier.Apply(ctx);
        foreach (var child in Outgoing) {
            child.Tgt.AssertToZ3(Graph.Ctx.MkAnd(child.SideConstraints.Select(o => o.ToExpr(ctx))));
            ctx.Push(child);
            Simplify(ctx);
            ctx.Pop();
        }
    }

    static int simplifyChainCnt;

    public static BacktrackReasons Simplify(NielsenContext ctx) {

        simplifyChainCnt++;
        int pushCnt = 0;

        void Fail() {
            for (var i = 0; i < pushCnt; i--) {
                // Inherit reason for only child
                ctx.CurrentNode.Reason = BacktrackReasons.ChildrenFailed;
                ctx.Pop();
            }
        }

        bool failedBefore = false;

        while (true) {
            if (ctx.Graph.OuterPropagator.Cancel)
                throw new Exception("Timeout");

            DetModifier mod = new();
            BacktrackReasons reason = ctx.CurrentNode.Simplify(ctx, mod.Substitutions, mod.SideConstraints);
            if (reason is not BacktrackReasons.Unevaluated && reason is not BacktrackReasons.Satisfied) {
                ctx.CurrentNode.Reason = reason;
                Fail();
                return reason;
            }

            if (mod.Trivial || failedBefore) {
                Debug.Assert(!failedBefore); // To avoid divergence in case of bugs - still this should better not happen (e.g., add n = 0 twice after each other)
                if (ctx.Graph.AddSumbsumptionCandidate(ctx.CurrentNode)) {
                    ctx.Pop(pushCnt);
                    return BacktrackReasons.Unevaluated;
                }
                ctx.CurrentNode.Reason = BacktrackReasons.Subsumption;
                Fail();
                return reason;
            }
            ctx.CurrentNode.Outgoing = [];
            mod.Apply(ctx);
            failedBefore = !mod.Success;
            Debug.Assert(ctx.CurrentNode.UnitNode);
            Debug.Assert(ctx.CurrentNode.Outgoing is not null);

            if (ctx.CurrentNode.Outgoing[0].SideConstraints.IsNonEmpty())
                ctx.CurrentNode.Outgoing[0].Tgt.AssertToZ3(ctx.Graph.Ctx.MkAnd(mod.SideConstraints.Select(o => o.ToExpr(ctx))));

            ctx.Push(ctx.CurrentNode.Outgoing![0]);
            pushCnt++;
        }
    }

    public void CollectSymbols(HashSet<NamedStrToken> vars, HashSet<SymCharToken> sChars, HashSet<IntVar> iVars, HashSet<CharToken> alphabet) {
        foreach (var cnstr in AllStrConstraints) {
            cnstr.CollectSymbols(vars, sChars, iVars, alphabet);
        }
    }

    static int simplifyCnt;

    public BacktrackReasons Simplify(NielsenContext ctx, List<Subst> substitution, HashSet<Constraint> newSideConstraints) {
        simplifyCnt++;
        Log.WriteLine("Simplify: " + simplifyCnt);
        bool restart = true;
        while (restart) {
            HashSet<Constraint> toRemove = [];
            restart = false;
            foreach (var c1 in AllConstraints) {
                if (c1.Satisfied)
                    continue;
                BacktrackReasons reason = BacktrackReasons.Unevaluated;
                switch (c1.Simplify(ctx, substitution, newSideConstraints, ref reason)) {
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
                        if (substitution.IsNonEmpty())
                            // Better we integrate the new information 
                            // otw., x...x = cxa...axc could give x / cx and x / xc but this "c" might be the same one
                            // so either try to unify the substitutions, or just apply every substitution as soon as we get it
                            return BacktrackReasons.Unevaluated;
                        break;
                    default:
                        throw new ArgumentOutOfRangeException();
                }
            }
            foreach (var c in toRemove) {
                RemoveConstraint(c);
            }
        }
        return BacktrackReasons.Unevaluated;
    }

    public void RemoveConstraint(Constraint c) {
        foreach (var cnstrSet in AllConstraintSets) {
            if (cnstrSet.Remove(c)) {
                // Because of rewriting there might be more than one occurrence of the same constraint
                while (cnstrSet.Remove(c)) {}
                return;
            }
        }
        Debug.Assert(false);
    }

    public NielsenNode MkChild(NielsenContext ctx, IReadOnlyList<Subst> subst, bool progress) {
        Debug.Assert(ctx.CurrentNode.Outgoing is not null);
        return new NielsenNode(ctx, subst, progress) {
            StrEq = StrEq.Clone(),
            IntEq = IntEq.Clone(),
            IntNEq = IntNEq.Clone(),
            IntLe = IntLe.Clone(),
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
        if (StrConstraintCnt != other.StrConstraintCnt || IntBounds.Count != other.IntBounds.Count || DisEq.Count != other.DisEq.Count)
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
        AllConstraintSets.Aggregate(164304773, (i, v) => i + 366005033 * Id);

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
            case IntNonEq iNEq:
                return IntNEq.Add(iNEq);
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
        reason is BacktrackReasons.DepthLimit ;

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
        if (IsResourceReason(r1) && IsResourceReason(r2)) {
            Debug.Assert(r1 == r2);
            return r1;
        }
        if (IsResourceReason(r1))
            return r1;
        if (IsResourceReason(r2))
            return r2;
        return BacktrackReasons.ChildrenFailed;
    }

    // TODO: Make iterative (not hard to do but hard to debug => do only when relatively stable!)
    public bool Check(NielsenContext ctx, int dep) {
        if (!Extended) {
            Status z3Res = Status.UNKNOWN;
            if (ProgressNode) {
                // We made progress - let's check if this is already enough to get an integer conflict
                // This can be expensive, so we only do this in case the formula simplified "strongly" before
                // => we ask Z3
                z3Res = Parent is null ? Graph.SubSolver.Check() : Graph.SubSolver.Check(Parent.Assumption);
                switch (z3Res) {
                    case Status.UNKNOWN:
                        throw new Exception("unknown");
                    case Status.UNSATISFIABLE:
                        Reason = BacktrackReasons.SMT;
                        return false;
                }
            }

            if (!AllStrConstraints.Any()) {
                // We might have already checked this if it was a progress node
                // We need a Z3 result so let's ask if we haven't already
                if (z3Res == Status.UNKNOWN) {
                    Debug.Assert(!ProgressNode);
                    z3Res = Parent is null ? Graph.SubSolver.Check() : Graph.SubSolver.Check(Parent.Assumption);
                }
                switch (z3Res) {
                    case Status.UNKNOWN:
                        throw new Exception("unknown");
                    // If Z3 says unsat, we backtrack
                    case Status.UNSATISFIABLE:
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
            Extend(ctx);
        }
        bool first = true;
        BacktrackReasons reason = Reason;
        Debug.Assert(Outgoing is not null);
        bool sat = false;
        foreach (var outgoing in Outgoing) {
            if (outgoing.Tgt is { IsConflict: false, IsSatisfied: false }) {
                outgoing.IncModCount(Graph);
                int modCnt = Graph.ModCnt;
                bool r = outgoing.Tgt.Check(ctx, dep + 1); // TODO: Don't increment on unit steps!
                Debug.Assert(modCnt == Graph.ModCnt);
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