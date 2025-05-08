using System.ComponentModel.Design;
using System.Diagnostics;
using System.Runtime.Serialization;
using System.Security.Cryptography;
using System.Text;
using System.Xml.Linq;
using Microsoft.Z3;
using StringBreaker.Constraints.ConstraintElement;
using StringBreaker.Constraints.Modifier;
using StringBreaker.IntUtils;
using StringBreaker.MiscUtils;
using StringBreaker.Tokens;

namespace StringBreaker.Constraints;

public enum BacktrackReasons {
    Unevaluated,
    // These are actual conflicts
    SymbolClash,
    ParikhImage,
    Subsumption,
    Arithmetic,
    SMT,
    ChildrenFailed,
}

public class NielsenNode {

    public int Id { get; }
    public NielsenGraph Graph { get; }

    public List<NielsenEdge> Outgoing { get; } = [];

    // These values are always the same as soon as simplified independent of forbidden edge
    public bool IsGeneralConflict { get; private set; }
    public bool IsExtended { get; private set; }

    // Blocking might affect those values so we might recompute them in different runs (because of forbidden edges)
    public bool IsCurrentlyConflict => IsGeneralConflict || (CurrentReason != BacktrackReasons.Unevaluated && IsExtended);

    // Reason why the node was a conflict - if it did not fail directly, it mostly says because of its children
    public BacktrackReasons CurrentReason { get; set; } = BacktrackReasons.Unevaluated;
    public bool IsActive => evalIdx == Graph.RunIdx;
    uint evalIdx;

    public NList<StrEq> StrEq { get; init; } = [];
    public NList<IntEq> IntEq { get; init; } = [];
    public NList<IntLe> IntLe { get; init; } = [];

    // e.g., o \notin { a, b, p }
    public Dictionary<SymCharToken, HashSet<UnitToken>> DisEqs { get; init; } = [];

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

    public void ResetCounter() => 
        evalIdx = 0;

    public NielsenNode(NielsenGraph graph) {
        Graph = graph;
        // Graph.PersistPending();
        Id = graph.NodeCnt;
        IsProgressNode = true;
        graph.AddNode(this);
        // graph.AddPending(this);
    }

    public NielsenNode(NielsenNode parent,
        IReadOnlyList<Subst> subst,
        IReadOnlyCollection<Constraint> sideConds,
        IReadOnlyCollection<DisEq> disEqs, 
        bool isProgress) : this(parent.Graph) {

        IsProgressNode = isProgress;
        FuncDecl f = Graph.Ctx.MkFreshConstDecl("P", Graph.Ctx.BoolSort);
        BoolExpr pathLit = (BoolExpr)Graph.Ctx.MkUserPropagatorFuncDecl(f.Name.ToString(), Array.Empty<Sort>(), Graph.Ctx.BoolSort).Apply();
        var outEdge = new NielsenEdge(parent, pathLit, subst, sideConds, disEqs, this);
        parent.Outgoing.Add(outEdge);

        // TODO: Delay this until we actually need it
        // Equate the lengths
        IntExpr[] lhs = new IntExpr[subst.Count];
        for (int i = 0; i < lhs.Length; i++) {
            lhs[i] = subst[i].KeyLenExpr(Graph);
            // |x| >= 0
            // TODO: Actually, we should already do this earlier...
            outEdge.AssertToZ3(Graph.Ctx.MkGe(lhs[i], Graph.Ctx.MkInt(0)));
        }
        int modCnt = Graph.ModCnt;
        outEdge.IncModCount(Graph);
        for (int i = 0; i < lhs.Length; i++) {
            var rhs = subst[i].ValueLenExpr(Graph);
            if (!lhs[i].Equals(rhs))
                // |x| = |u|
                outEdge.AssertToZ3(Graph.Ctx.MkEq(lhs[i], rhs));
        }
        foreach (var cond in sideConds) {
            if (cond is StrEq)
                // We do not have to report on equality decomposition
                // ... not really of interest for the outer solver
                continue;
            outEdge.AssertToZ3(cond.ToExpr(Graph));
        }
        foreach (var disEq in disEqs) {
            outEdge.AssertToZ3(disEq.ToExpr(Graph));
        }
        outEdge.DecModCount(Graph);
        Debug.Assert(Graph.ModCnt == modCnt);
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
                AddConstraints(ConstraintElement.IntLe.MkLe(new IntPoly((BigInt)bound.Min), n.Clone()));
            else if (bound.HasHigh)
                AddConstraints(ConstraintElement.IntLe.MkLe(new IntPoly(watched), n.Clone()));
        }
        VarBoundWatcher.Remove(v.Var);
    }

    public bool IsIntFixed(NonTermInt v, out BigIntInf val) {
        val = default;
        if (!IntBounds.TryGetValue(v, out var bounds)) 
            return false;
        val = bounds.Min;
        return bounds.IsUnit;
    }
    public bool IsBoundLower(NonTermInt v, out BigIntInf val) {
        val = default;
        if (!IntBounds.TryGetValue(v, out var bounds)) 
            return false;
        val = bounds.Min;
        return bounds.Min.IsNegInf;
    }

    public bool IsBoundUpper(NonTermInt v, out BigIntInf val) {
        val = default;
        if (!IntBounds.TryGetValue(v, out var bounds)) 
            return false;
        val = bounds.Max;
        return bounds.Max.IsPosInf;
    }

    void WatchVarBound(NonTermInt v) {
        NonTermSet nonTermSet = new();
        v.CollectSymbols(nonTermSet, []);
        foreach (var var in nonTermSet.StrVars) {
            if (!VarBoundWatcher.TryGetValue(var, out var watched))
                VarBoundWatcher.Add(var, watched = []);
            watched.Add(v);
        }
    }

    public SimplifyResult AddLowerIntBound(NonTermInt v, BigIntInf val) {
        Debug.Assert(val != BigIntInf.PosInf);
        val = BigIntInf.Max(val, v.MinLen);
        Interval i;
        if (val == v.MinLen)
            // Not very helpful
            return SimplifyResult.Proceed;
        if (!IntBounds.TryGetValue(v, out var bounds)) {
            WatchVarBound(v);
            i = new Interval(val, BigIntInf.PosInf);
            IntBounds.Add(v, i);
            //AssertToZ3(i.ToZ3Constraint(v, Graph));
            return SimplifyResult.Restart;
        }
        if (val > bounds.Max)
            return SimplifyResult.Conflict;
        if (val <= bounds.Min)
            return SimplifyResult.Proceed;
        i = new Interval(val, bounds.Max);
        IntBounds[v] = i;
        //AssertToZ3(i.ToZ3Constraint(v, Graph));
        return SimplifyResult.Restart;
    }

    public SimplifyResult AddHigherIntBound(NonTermInt v, BigIntInf val) {
        Debug.Assert(val != BigIntInf.NegInf);
        if (val < v.MinLen)
            return SimplifyResult.Conflict;
        if (val.IsPosInf)
            // Not very helpful
            return SimplifyResult.Proceed;
        Interval i;
        if (!IntBounds.TryGetValue(v, out var bounds)) {
            WatchVarBound(v);
            i = new Interval(v is LenVar ? 0 : BigIntInf.NegInf, val);
            IntBounds.Add(v, i);
            //AssertToZ3(i.ToZ3Constraint(v, Graph));
            return SimplifyResult.Restart;
        }
        if (val < bounds.Min)
            return SimplifyResult.Conflict;
        if (val >= bounds.Max)
            return SimplifyResult.Proceed;
        i = new Interval(bounds.Min, val);
        IntBounds[v] = i;
        //AssertToZ3(i.ToZ3Constraint(v, Graph));
        return SimplifyResult.Restart;
    }

    public bool ConsistentIntVal(IntVar var, BigIntInf v) => 
        !IntBounds.TryGetValue(var, out var bounds) || bounds.Contains(v);

    // lhs == rhs
    // No need to copy anything!
    public bool IsEq(IntPoly lhs, IntPoly rhs) {
        IntEq eq = new(lhs.Clone(), rhs);
        return eq.Simplify(this) switch {
            SimplifyResult.Satisfied => true,
            SimplifyResult.Conflict => false,
            _ => IntEq.Contains(eq),
        };
    }

    // p == 0 || p <= 0 [for implementation syntactic reasons, p == 0 can be true and p <= 0 can be false]
    // No need to copy anything!
    public bool IsPowerElim(IntPoly p) => IsZero(p) || IsNonPos(p);

    // p == 0
    // No need to copy anything!
    public bool IsZero(IntPoly p) => IsEq(p, new IntPoly());

    // p == 1
    // No need to copy anything!
    public bool IsOne(IntPoly p) => IsEq(p, new IntPoly(1));

    // lhs <= rhs
    // lhs - rhs <= 0
    // No need to copy anything!
    public bool IsLe(IntPoly lhs, IntPoly rhs) {
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
    public bool IsLt(IntPoly lhs, IntPoly rhs) {
        IntLe le = ConstraintElement.IntLe.MkLt(lhs.Clone(), rhs);
        return le.Simplify(this) switch {
            SimplifyResult.Satisfied => true,
            SimplifyResult.Conflict => false,
            _ => IntLe.Contains(le),
        };
    }

    // p < 0
    // No need to copy anything!
    public bool IsNeg(IntPoly p) => IsLt(p, new IntPoly());

    // p <= 0
    // No need to copy anything!
    public bool IsNonPos(IntPoly p) => IsLe(p, new IntPoly());

    // p > 0
    // No need to copy anything!
    public bool IsPos(IntPoly p) => IsLt(new IntPoly(), p);

    // p >= 0
    // No need to copy anything!
    public bool IsNonNeg(IntPoly p) => IsLe(new IntPoly(), p);

    // Just express one variable in each equation and substitute it everywhere
    Dictionary<NonTermInt, RatPoly> ResolveIntEqs() {
        List<RatPoly> expressed = [];
        Dictionary<NonTermInt, int> eliminated = [];

        foreach (var eq in IntEq) {
            HashSet<NonTermInt> nonLinear = [];
            Dictionary<NonTermInt, BigInt> linear = [];
            foreach (var v in eq.Poly) {
                if (v.t.Count == 1) {
                    var n = v.t.First();
                    if (n.occ.IsOne) {
                        if (eliminated.ContainsKey(n.t) || nonLinear.Contains(n.t))
                            continue;
                        linear.Add(n.t, n.occ);
                    }
                    else {
                        nonLinear.Add(n.t);
                        linear.Remove(n.t);
                    }
                    continue;
                }
                foreach (var v2 in v.t) {
                    nonLinear.Add(v2.t);
                    linear.Remove(v2.t);
                }
            }

            if (linear.IsEmpty())
                continue;
            (NonTermInt bestVar, BigInt bestCoeff) = linear.First();
            bestCoeff = bestCoeff.Abs();
            foreach (var l in linear) {
                var cr = l.Value.Abs();
                if (cr >= bestCoeff)
                    continue;
                bestVar = l.Key;
                bestCoeff = cr;
            }
            Debug.Assert(!bestCoeff.IsZero);
            Debug.Assert(!eliminated.ContainsKey(bestVar));

            var def = eq.Poly.ToRatPoly();
            def.Sub(new BigRat(bestCoeff), new StrictMonomial(bestVar));
            def = def.Div(new BigRat(bestCoeff));
            for (int j = 0; j < expressed.Count; j++) {
                var e = expressed[j];
                expressed[j] = e.Apply(bestVar, def);
            }
            eliminated.Add(bestVar, expressed.Count);
            expressed.Add(def);
        }
        Dictionary<NonTermInt, RatPoly> result = [];
        foreach (var (v, i) in eliminated) {
            result.Add(v, expressed[i]);
        }
        return result;
    }

    public bool AreDiseq(UnitToken u1, UnitToken u2) {
        SymCharToken s;
        if (u1 is CharToken c1) {
            if (u2 is CharToken c2)
                return !c1.Equals(c2);
            s = (SymCharToken)u2;
        }
        else
            s = (SymCharToken)u1;
        return DisEqs.TryGetValue(s, out var disEqs) && disEqs.Contains(u1);
    }

    public void Extend() {
        // get minimal split
        Debug.Assert(StrEq.Count > 0);
        Debug.Assert(!IsExtended);
        Debug.Assert(Outgoing.Count == 0);
        ModifierBase? bestModifier = null;

        Dictionary<NonTermInt, RatPoly> intSubst = ResolveIntEqs();

        foreach (var cnstr in StrEq) {
            ModifierBase currentModifier = cnstr.Extend(this, intSubst);
            if (bestModifier is null || currentModifier.CompareTo(bestModifier) < 0)
                bestModifier = currentModifier;
        }
        Debug.Assert(bestModifier is not null);
        bestModifier.Apply(this);
        IsExtended = true;
        foreach (var child in Outgoing) {
            int modCnt = Graph.ModCnt;
            child.IncModCount(Graph);
            SimplifyAndInit(child.Tgt, child);
            child.DecModCount(Graph);
            Debug.Assert(modCnt == Graph.ModCnt);
        }
    }

    static int simplifyChainCnt;

    public static BacktrackReasons SimplifyAndInit(NielsenNode node, NielsenEdge? edge) {
        // we need to track the last edge to change the target on subsumption
        Debug.Assert(edge is null || ReferenceEquals(node, edge.Tgt));
        if (node.IsCurrentlyConflict)
            return node.CurrentReason;

        //node.Graph.PersistPending();

        List<NielsenEdge> edgeChain = [];
        simplifyChainCnt++;

        void Fail() {
            for (var i = edgeChain.Count; i > 0; i--) {
                // Inherit reason for only child
                Debug.Assert(edgeChain[i - 1].Src.Outgoing.Count == 1);
                edgeChain[i - 1].Src.CurrentReason = BacktrackReasons.ChildrenFailed;
                edgeChain[i - 1].DecModCount(node.Graph);
            }
        }

        while (true) {
            if (node.Graph.OuterPropagator.Cancel)
                throw new SolverTimeoutException();
            node.evalIdx = node.Graph.RunIdx;

            NonTermSet modSet = edge?.GetNonTermModSet() ?? new NonTermSet();
            DetModifier outSideCnstr = new();
            var reason = node.Simplify(modSet, outSideCnstr, false);
            if (reason is not BacktrackReasons.Unevaluated) {
                node.IsGeneralConflict = true;
                node.CurrentReason = reason;
                Fail();
                return reason;
            }

            if (outSideCnstr.Trivial) {
                //var existing = node.Graph.FindExisting(node);
                //if (edge is not null && existing is not null) {
                //    edge.Tgt = existing; // Take the existing node
                //    // Hard to delete the existing node so let's keep it pending...
                //    Debug.Assert(node.Outgoing.IsEmpty());
                //    node.evalIdx = 0;
                //    Debug.Assert(edge.Src.IsExtended);
                //}

                for (var i = edgeChain.Count; i > 0; i--) {
                    edgeChain[i - 1].DecModCount(node.Graph);
                }
                return BacktrackReasons.Unevaluated;

            }
            // not subsumed, so we need to keep the node
            // node.Graph.PersistPending();

            outSideCnstr.Apply(node);
            node.IsExtended = true;
            Debug.Assert(node.Outgoing.Count == 1);

            edge = node.Outgoing[0];

            if (edge.SideConstraints.IsNonEmpty())
                edge.AssertToZ3(node.Graph.Ctx.MkAnd(outSideCnstr.SideConstraints.Where(o => o is not ConstraintElement.StrEq).Select(o => o.ToExpr(node.Graph))));

            edge.IncModCount(node.Graph);
            node = edge.Tgt;
            edgeChain.Add(edge);
        }
    }

    public void CollectSymbols(NonTermSet nonTermSet, HashSet<CharToken> alphabet) {
        foreach (var cnstr in StrEq) {
            cnstr.CollectSymbols(nonTermSet, alphabet);
        }
    }

    static int simplifyCnt;

    public BacktrackReasons Simplify(NonTermSet modSet, DetModifier outSideCnstr, bool forceRewriteAll) {
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
                switch (c.SimplifyAndPropagate(this, modSet, outSideCnstr, ref reason, forceRewriteAll)) {
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
            if (!outSideCnstr.Trivial)
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
            eq.SimplifyUnitNielsen(outSideCnstr, forwardVarDep, true);
            eq.SimplifyUnitNielsen(outSideCnstr, backwardVarDep, false);
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
        Log.Verify(StrEq.Remove(toRemove));
        while (StrEq.Remove(toRemove)) {}
    }

    public void RemoveIntEq(IntEq toRemove) {
        Log.Verify(IntEq.Remove(toRemove));
        while (IntEq.Remove(toRemove)) {}
    }

    public void RemoveIntLe(IntLe toRemove) {
        Log.Verify(IntLe.Remove(toRemove));
        while (IntLe.Remove(toRemove)) {}
    }

    public void RemoveDisEq(DisEq disEq0) {
        DisEq? disEq = disEq0;
        if (!DisEqs.TryGetValue(disEq.O, out var list)) {
            Debug.Assert(false);
            return;
        }
        Log.Verify(list.Remove(disEq.U));
        if (list.IsEmpty())
            DisEqs.Remove(disEq.O);
        if (!disEq.IsInverse(out disEq))
            return;
        Log.Verify(DisEqs.TryGetValue(disEq.O, out list));
        Debug.Assert(list is not null);
        Log.Verify(list.Remove(disEq.U));
        if (list.IsEmpty())
            DisEqs.Remove(disEq.O);
    }

    public NielsenNode MkChild(NielsenNode parent,
        IReadOnlyList<Subst> subst,
        IReadOnlyCollection<Constraint> sideConds,
        IReadOnlyCollection<DisEq> disEqs, bool progress) {

        var child = new NielsenNode(parent, subst, sideConds, disEqs, progress) {
            StrEq = StrEq.Select(o => o.Clone()).ToNList(),
            IntEq = IntEq.Select(o => o.Clone()).ToNList(),
            IntLe = IntLe.Select(o => o.Clone()).ToNList(),
            IntBounds = new Dictionary<NonTermInt, Interval>(IntBounds),
            VarBoundWatcher = VarBoundWatcher.ToDictionary(o => o.Key, o => o.Value.ToHashSet()),
            DisEqs = DisEqs.ToDictionary(o => o.Key, o => o.Value.ToHashSet()),
        };
        // First apply the substitutions
        foreach (var s in subst) {
            child.Apply(s);
        }
        // ... then add the new stuff
        foreach (var cond in sideConds) {
            child.AddConstraints(cond.Clone());
        }
        foreach (var disEq in disEqs) {
            child.AddDisEq(disEq);
        }
        return child;
    }

    public NielsenNode Clone() {
        return new NielsenNode(Graph) {
            StrEq = StrEq.Select(o => o.Clone()).ToNList(),
            IntEq = IntEq.Select(o => o.Clone()).ToNList(),
            IntLe = IntLe.Select(o => o.Clone()).ToNList(),
            IntBounds = new Dictionary<NonTermInt, Interval>(IntBounds),
            VarBoundWatcher = VarBoundWatcher.ToDictionary(o => o.Key, o => o.Value.ToHashSet()),
            DisEqs = DisEqs.ToDictionary(o => o.Key, o => o.Value.ToHashSet()),
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
        if (StrEq.Count != other.StrEq.Count || IntBounds.Count != other.IntBounds.Count || DisEqs.Count != other.DisEqs.Count)
            return false;
        foreach (var cnstrPair in AllConstraints.Zip(other.AllConstraints)) {
            if (!cnstrPair.First.Equals(cnstrPair.Second))
                return false;
        }
        foreach (var (v, i) in IntBounds) {
            if (!other.IntBounds.TryGetValue(v, out var i2) || i != i2)
                return false;
        }
        foreach (var (v, d1) in DisEqs) {
            if (!other.DisEqs.TryGetValue(v, out var d2))
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

    public bool AddDisEq(DisEq disEq0) {
        DisEq? disEq = disEq0;
        if (!DisEqs.TryGetValue(disEq.O, out var list))
            DisEqs.Add(disEq.O, list = []);
        if (!list.Add(disEq.U))
            return false;
        if (!disEq.IsInverse(out disEq))
            return true;
        if (!DisEqs.TryGetValue(disEq.O, out list))
            DisEqs.Add(disEq.O, list = []);
        Log.Verify(list.Add(disEq.U));
        return true;
    }

    // Checks if stronger is more constrained than this
    public bool Subsumes(NielsenNode stronger) {
        Debug.Assert(stronger.StrEq.Equals(StrEq));
        return EqualContent(stronger);
        //if (!BoundsSubsumes(stronger))
        //    return false;
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

    public static bool IsActualConflict(BacktrackReasons reason) =>
        IsConflictReason(reason) && reason != BacktrackReasons.ChildrenFailed;

    public static string ReasonToString(BacktrackReasons reason) => reason switch {
        BacktrackReasons.Unevaluated => "Unevaluated",
        BacktrackReasons.SymbolClash => "Symbol Clash",
        BacktrackReasons.ParikhImage => "Parikh Image",
        BacktrackReasons.Arithmetic => "Arithmetic",
        BacktrackReasons.Subsumption => "Subsumption",
        BacktrackReasons.SMT => "SMT",
        BacktrackReasons.ChildrenFailed => "Children Failed",
        _ => throw new ArgumentOutOfRangeException(),
    };

    void Activate() {
        if (IsActive) 
            return;
        evalIdx = Graph.RunIdx;
        CurrentReason = BacktrackReasons.Unevaluated;
    }

    bool IsSkipEdge(NielsenEdge edge, HashSet<BoolExpr> forbidden, HashSet<BoolExpr> usedForbidden) {
        if (edge.Tgt.IsGeneralConflict)
            // it is a contradiction independent of the forbidden edges
            return true;
        if (edge.Tgt is { IsActive: true, IsCurrentlyConflict: true })
            // We already marked it conflicting in a previous iterative deepening round
            return true;
        if (forbidden.Contains(edge.Assumption)) {
            // The outer SMT solver has blocked this path
            // Otw. it might not necessarily be a conflict
            Log.Verify(!usedForbidden.Add(edge.Assumption));
            return true;
        }
        return false;
    }

    static int checkCnt;

    // Unit and progression steps are not countered for depth bound
    public SolveResult Check(int dep, HashSet<BoolExpr> forbidden, HashSet<BoolExpr> usedForbidden) {
        Debug.Assert(Graph.RunIdx > 0);

        // The node could be from a different run - reset its values
        Activate();

        if (IsCurrentlyConflict)
            return SolveResult.UNSAT;

#if DEBUG
        int localCheck = checkCnt;
        checkCnt++;

        if (Graph.CurrentPath.Count > 1000)
            Console.WriteLine("Suspiciously deep nesting...");
#endif

        Debug.Assert(IsActive);

        if (!IsExtended) {
            Status z3Res = Status.UNKNOWN;
            if (IsProgressNode) {
                // We made progress - let's check if this is already enough to get an integer conflict
                // This can be expensive, so we only do this in case the formula simplified "strongly" before
                // => we ask Z3
                z3Res = Graph.SubSolver.Check(Graph.CurrentPath.Select(o => o.Assumption));
                if (z3Res == Status.UNKNOWN) {
                    if (Graph.SubSolver.ReasonUnknown is "timeout" or "canceled")
                        throw new SolverTimeoutException();
                    throw new Exception("Z3 returned unknown");
                }

                if (z3Res == Status.UNSATISFIABLE) {
                    Debug.Assert(Outgoing.IsEmpty());
                    CurrentReason = BacktrackReasons.SMT;
                    IsExtended = true;
                    Debug.Assert(IsCurrentlyConflict);
                    return SolveResult.UNSAT;
                }
            }

            if (StrEq.Count == 0) {
                // We might have already checked this if it was a progress node
                // We need a Z3 result so let's ask if we haven't already
                if (z3Res == Status.UNKNOWN) {
                    Debug.Assert(!IsProgressNode);
                    z3Res = Graph.SubSolver.Check(Graph.CurrentPath.Select(o => o.Assumption));
                }
                if (z3Res == Status.UNKNOWN) {
                    if (Graph.SubSolver.ReasonUnknown is "timeout" or "canceled")
                        throw new SolverTimeoutException();
                    throw new Exception("Z3 returned unknown");
                }
                // If Z3 says unsat, we backtrack
                if (z3Res == Status.UNSATISFIABLE) {
                    CurrentReason = BacktrackReasons.SMT;
                    Debug.Assert(IsCurrentlyConflict);
                    return SolveResult.UNSAT;
                }
                // Otw. we found a candidate model
                // Graph.PersistPending();
                Debug.Assert(!IsCurrentlyConflict);
                return SolveResult.SAT;
            }
            if (dep > Graph.DepthBound)
                return SolveResult.UNKNOWN;
            Extend();
        }

        bool generalConflict = true; // are all children unsat independent of the path?
        bool gotUnknown = false; // did at least one child fail because of some resource limit?

        Debug.Assert(CurrentReason == BacktrackReasons.Unevaluated);
        Debug.Assert(IsActive);
        Debug.Assert(IsExtended);
        Debug.Assert(!IsCurrentlyConflict);

        // TODO: Set a node contradiction if all of its children are contradictions (no matter if forbidden or not)
        foreach (var outgoing in Outgoing) {
            if (IsSkipEdge(outgoing, forbidden, usedForbidden))
                continue;
            Debug.Assert(outgoing.Tgt.evalIdx <= Graph.RunIdx);
            outgoing.IncModCount(Graph);
            int modCnt = Graph.ModCnt;
            // we want to go deep fast if there is no danger of divergence
            int nextDep = outgoing.Tgt.IsProgressNode ? dep : dep + 1;
            switch (outgoing.Tgt.Check(nextDep, forbidden, usedForbidden)) {
                case SolveResult.SAT:
                    return SolveResult.SAT;
                case SolveResult.UNSAT:
                    generalConflict &= outgoing.Tgt.IsGeneralConflict;
                    break;
                case SolveResult.UNKNOWN:
                    gotUnknown = true;
                    break;
                default:
                case SolveResult.UNSOUND:
                    throw new Exception("Subcall returned unsound");
            }

            Debug.Assert(modCnt == Graph.ModCnt);
            outgoing.DecModCount(Graph);
        }

        if (gotUnknown) {
            // We hit at lease once a depth-limit
            Debug.Assert(CurrentReason == BacktrackReasons.Unevaluated);
            return SolveResult.UNKNOWN;
        }

        // All children are inconsistent
        Debug.Assert(!IsGeneralConflict || generalConflict);
        IsGeneralConflict = generalConflict; // if all children failed generally, this node also fails generally
        if (Outgoing.IsNonEmpty())
            CurrentReason = BacktrackReasons.ChildrenFailed;
        return SolveResult.UNSAT;
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
        if (DisEqs.IsNonEmpty()) {
            sb.AppendLine("DisEqs:");
            foreach (var (v, deq) in DisEqs) {
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
}