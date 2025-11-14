using Microsoft.Z3;
using System.Collections.Generic;
using System.Diagnostics;
using System.Numerics;
using System.Runtime.InteropServices;
using System.Security.Cryptography;
using System.Text;
using System.Text.RegularExpressions;
using ZIPT.Constraints.ConstraintElement;
using ZIPT.Constraints.Modifier;
using ZIPT.IntUtils;
using ZIPT.MiscUtils;
using ZIPT.Strings.Chunks;
using ZIPT.Strings.Tokens;
using ZIPT.Strings.Tokens.RegexTokens;

namespace ZIPT.Constraints;

public enum BacktrackReasons {
    Unevaluated,
    // These are actual conflicts
    SymbolClash,
    ParikhImage,
    Subsumption,
    Arithmetic,
    Regex,
    RegexWidening,
    CharacterRange,
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
    IEnumerator<NielsenEdge>? extensionEnum;

    // Blocking might affect those values so we might recompute them in different runs (because of forbidden edges)
    public bool IsCurrentlyConflict =>
        IsGeneralConflict || (CurrentReason != BacktrackReasons.Unevaluated && IsExtended);

    // Reason why the node was a conflict - if it did not fail directly, it mostly says because of its children
    public BacktrackReasons CurrentReason { get; set; } = BacktrackReasons.Unevaluated;
    public bool IsActive => evalIdx == Graph.RunIdx;
    uint evalIdx;

    public NList<StrEq> ConstraintsStrEq { get; init; } = [];

    public Dictionary<uint, StrMem> ConstraintsStrMem { get; init; } = [];

    //public NList<ReSplit> ConstraintsReSplit { get; init; } = [];
    public NList<IntEq> ConstraintsIntEq { get; init; } = [];
    public NList<IntLe> ConstraintsIntLe { get; init; } = [];
    public Dictionary<SymCharToken, List<SymCharToken>> DisEqualities { get; init; } = [];
    public Dictionary<SymCharToken, CharacterSet> CharRanges { get; init; } = [];

    public IEnumerable<Constraint> AllConstraints =>
        ConstraintsStrEq.OfType<Constraint>()
            .Concat(ConstraintsStrMem.Select(o => o.Value))
            //.Concat(ConstraintsReSplit)
            .Concat(ConstraintsIntEq)
            .Concat(ConstraintsIntLe);

    public Environment Env => Graph.Env;

    // A node is marked as progress if either
    // 1) it is root
    // 2) it results from a node by adding some eliminating substitution (e.g., x / y or x / "" or x / a^n)
    // 3) it results from a node by adding a strong side constraint (e.g., n = 0 or splitting some equation)
    // We only check progress nodes and potentially satisfied nodes by a call to Z3
    public bool IsProgressNode { get; }

    // x \in [i, j] with i, j const
    public Dictionary<NamedInt, Interval<BigInteger>> IntBounds { get; init; } = [];

    // Bounds for e.g., |x| might change when substituting x - we associate x with relevant integer variables depending on it
    public Dictionary<NamedStrToken, HashSet<NamedInt>> VarBoundWatcher { get; init; } = [];

    // x... = uy... and u ground
    // If multiple x... = vy... then we keep one of them (preferably the shorter one)
    // We just cache it, as both simplify and splitting need this (no need to clone)
    public readonly Dictionary<NamedStrToken, Dictionary<NamedStrToken, List<StrToken>>>
        forwardVarDep = []; // x... = uy... => (x, y) -> u 

    public readonly Dictionary<NamedStrToken, Dictionary<NamedStrToken, List<StrToken>>>
        backwardVarDep = []; // ...x = ...yu => (x, y) -> u 

    public void ResetCounter() =>
        evalIdx = 0;

    public NielsenNode(NielsenGraph graph) {
        Graph = graph;
        Id = graph.NodeCnt;
        IsProgressNode = true;
        graph.AddNode(this);
    }

    public NielsenNode(NielsenGraph graph, NielsenNode parent) : this(graph) {
        ConstraintsStrEq = new NList<StrEq>(parent.ConstraintsStrEq.Count);
        ConstraintsStrMem = new Dictionary<uint, StrMem>(parent.ConstraintsStrMem.Count);
        ConstraintsIntEq = new NList<IntEq>(parent.ConstraintsIntEq.Count);
        ConstraintsIntLe = new NList<IntLe>(parent.ConstraintsIntLe.Count);
        foreach (var e in parent.ConstraintsStrEq) {
            ConstraintsStrEq.Add(new StrEq(e.LHS, e.RHS));
        }
        foreach (var e in parent.ConstraintsStrMem) {
            Debug.Assert(e.Key == e.Value.Id);
            ConstraintsStrMem.Add(e.Key, new StrMem(e.Value.Str, e.Value.Regex, e.Value.History, e.Value.Id));
        }
        foreach (var e in parent.ConstraintsIntEq) {
            ConstraintsIntEq.Add(new IntEq(e.Poly));
        }
        foreach (var e in parent.ConstraintsIntLe) {
            ConstraintsIntLe.Add(new IntLe(e.Poly));
        }
        foreach (var e in parent.DisEqualities) {
            DisEqualities.Add(e.Key, e.Value.ToList());
        }
        foreach (var e in parent.CharRanges) {
            CharRanges.Add(e.Key, e.Value.Clone());
        }

        IntBounds = new Dictionary<NamedInt, Interval<BigInteger>>(parent.IntBounds);
        VarBoundWatcher = new Dictionary<NamedStrToken, HashSet<NamedInt>>();
        foreach (var e in parent.VarBoundWatcher) {
            VarBoundWatcher.Add(e.Key, [..e.Value]);
        }

    }

    public NielsenNode(LocalInfo info,
        IReadOnlyList<Subst> subst,
        IReadOnlyList<CharSubst> substC,
        IReadOnlyCollection<Constraint> sideConds,
        bool isProgress) : this(info.CurrentNode.Graph, info.CurrentNode) {

        IsProgressNode = isProgress;
        var outEdge = new NielsenEdge(info.CurrentNode, subst, substC, sideConds, this);
        info.CurrentNode.Outgoing.Add(outEdge);

        // TODO: Delay this until we actually need it
        // Equate the lengths
        IntExpr[] lhs = new IntExpr[subst.Count];
        for (int i = 0; i < lhs.Length; i++) {
            if (!subst[i].Var.RegexFree)
                continue;
            lhs[i] = subst[i].KeyLenExpr(Env, info.CurrentModificationCnt);
            // |x| >= 0
            // TODO: Actually, we should already do this earlier...
            outEdge.AddZ3Constraint(Graph.Ctx.MkGe(lhs[i], Graph.Ctx.MkInt(0)));
        }
        int modCnt = info.ModCnt;
        outEdge.IncModCount(info);
        for (int i = 0; i < lhs.Length; i++) {
            if (!subst[i].Var.RegexFree || !subst[i].Str.RegexFree)
                continue;
            var rhs = subst[i].ValueLenExpr(Env, info.CurrentModificationCnt);
            if (!lhs[i].Equals(rhs))
                // |x| = |u|
                outEdge.AddZ3Constraint(Graph.Ctx.MkEq(lhs[i], rhs));
        }
        foreach (var cond in sideConds) {
            if (!cond.Shared)
                // ... not really of interest for the outer solver
                continue;
            outEdge.AddZ3Constraint(cond.ToExpr(info));
        }
        outEdge.DecModCount(info);
        Debug.Assert(info.ModCnt == modCnt);
    }

    void Update<T>(NList<T> constraints, Subst subst, NielsenNode node) where T : Constraint, IComparable<T> {
        List<T> toAdd = [];
        List<T> toRemove = [];
        foreach (var cnstr in constraints) {
            var res = (T)cnstr.Apply(subst, node);
            if (!ReferenceEquals(res, cnstr)) {
                toRemove.Add(cnstr);
                toAdd.Add(res);
            }
        }
        foreach (var old in toRemove) {
            constraints.Remove(old);
        }
        foreach (var @new in toAdd) {
            constraints.Add(@new);
        }
    }

    void Update<T>(Dictionary<uint, T> constraints, Subst subst, NielsenNode node)
        where T : Constraint, IComparable<T> {
        List<(uint id, T v)> toChange = [];
        foreach (var cnstr in constraints) {
            var res = (T)cnstr.Value.Apply(subst, node);
            if (!ReferenceEquals(res, cnstr.Value)) {
                toChange.Add((cnstr.Key, res));
            }
        }
        foreach (var c in toChange) {
            Debug.Assert(constraints.ContainsKey(c.id));
            constraints[c.id] = c.v;
        }
    }

    void Update<T>(NList<T> constraints, CharSubst subst, NielsenNode node) where T : Constraint, IComparable<T> {
        List<T> toAdd = [];
        List<T> toRemove = [];
        foreach (var cnstr in constraints) {
            var res = (T)cnstr.Apply(subst, node);
            if (!ReferenceEquals(res, cnstr)) {
                toRemove.Add(cnstr);
                toAdd.Add(res);
            }
        }
        foreach (var old in toRemove) {
            constraints.Remove(old);
        }
        foreach (var @new in toAdd) {
            constraints.Add(@new);
        }
    }

    void Update<T>(Dictionary<uint, T> constraints, CharSubst subst, NielsenNode node)
        where T : Constraint, IComparable<T> {
        List<(uint id, T v)> toChange = [];
        foreach (var cnstr in constraints) {
            var res = (T)cnstr.Value.Apply(subst, node);
            if (!ReferenceEquals(res, cnstr.Value)) {
                toChange.Add((cnstr.Key, res));
            }
        }
        foreach (var c in toChange) {
            Debug.Assert(constraints.ContainsKey(c.id));
            constraints[c.id] = c.v;
        }
    }

    public void Apply(Subst subst, NielsenNode node) {
        Update(ConstraintsStrEq, subst, node);
        Update(ConstraintsStrMem, subst, node);
        Update(ConstraintsIntEq, subst, node);
        Update(ConstraintsIntLe, subst, node);
        if (!VarBoundWatcher.TryGetValue(subst.Var, out var watch))
            return;

        foreach (var watched in watch) {
            var bound = IntBounds[watched];
            IntBounds.Remove(watched);
            if (watched is not LenVar lv || !lv.Var.Equals(subst.Var)) {
                Debug.Assert(false);
                continue;
            }
            var n = subst.GetLenReplacement(Env).newLen;
            if (bound.HasLow)
                AddConstraint(IntLe.MkLe(Env.IntPDDManager.MkPDD((BigInteger)bound.Min), n));
            else if (bound.HasHigh)
                AddConstraint(IntLe.MkLe(Env.IntPDDManager.MkPDD(watched), n));
        }
        VarBoundWatcher.Remove(subst.Var);
    }

    public void Apply(CharSubst subst, NielsenNode node) {
        Update(ConstraintsStrEq, subst, node);
        Update(ConstraintsStrMem, subst, node);

        if (subst.Val is SymCharToken v) {
            if (DisEqualities.TryGetValue(subst.Var, out var list)) {
                foreach (var v2 in list) {
                    if (v2.Equals(v)) {
                        CurrentReason = BacktrackReasons.CharacterRange;
                        IsGeneralConflict = true;
                        return;
                    }
                }
                Log.Verify(DisEqualities.Remove(subst.Var));
                CharRanges.Remove(subst.Var);
            }
        }
        else if (subst.Val is CharToken c) {
            if (CharRanges.TryGetValue(subst.Var, out CharacterSet? s)) {
                if (!s.Contains(c)) {
                    CurrentReason = BacktrackReasons.CharacterRange;
                    IsGeneralConflict = true;
                    return;
                }
                DisEqualities.Remove(subst.Var);
                Log.Verify(CharRanges.Remove(subst.Var));
            }
            else {
                Debug.Assert(false);
            }
        }
    }

    public (Str s1, Str s2)[] GetSignature(Environment env, bool fwd) {
        int[] indices = new int[ConstraintsStrEq.Count * 2];
        Str[] str = new Str[ConstraintsStrEq.Count * 2];
        HashSet<NamedStrToken>[] processed = new HashSet<NamedStrToken>[ConstraintsStrEq.Count * 2];
        for (int i = 0; i < ConstraintsStrEq.Count; i++) {
            str[2 * i] = ConstraintsStrEq[i].LHS;
            str[2 * i + 1] = ConstraintsStrEq[i].RHS;
            processed[2 * i] = [];
            processed[2 * i + 1] = [];
        }

        for (int i = 0; i < indices.Length; i++) {
            if (indices[i] > 0)
                continue;
            var s = str[i][fwd];
            if (str[i].Length == 0)
                continue;
            indices[i]++;
            if (s is not NamedStrToken v)
                continue;
            for (int j = 0; j < indices.Length; j++) {
                if (i == j)
                    continue;
                if (indices[j] >= str[j].Length || processed[j].Contains(v))
                    continue;
                for (; indices[j] < str[j].Length; indices[j]++) {
                    if (str[j][fwd] is not NamedStrToken w)
                        continue;
                    processed[j].Add(w);
                    if (v.Equals(w))
                        break;
                }
            }
        }
        (Str s1, Str s2)[] res = new (Str, Str)[ConstraintsStrEq.Count];
        for (int i = 0; i < res.Length; i++) {
            res[i] = (
                env.StrManager.Extract(ConstraintsStrEq[i].LHS, (uint)indices[2 * i], fwd),
                env.StrManager.Extract(ConstraintsStrEq[i].RHS, (uint)indices[2 * i + 1], fwd)
            );
        }
        return res;
    }


    public bool IsIntFixed(NamedInt v, out InfNum<BigInteger> val) {
        val = default;
        if (!IntBounds.TryGetValue(v, out var bounds))
            return false;
        val = bounds.Min;
        return bounds.IsUnit;
    }

    public Interval<BigInteger> GetBounds(NamedInt v) {
        if (!IntBounds.TryGetValue(v, out var bounds))
            return new Interval<BigInteger>(v.MinLen, InfNum<BigInteger>.PosInfNum);
        return bounds;
    }

    public InfNum<BigInteger> GetBoundLower(NamedInt v) {
        if (!IntBounds.TryGetValue(v, out var bounds))
            return v.MinLen;
        return bounds.Min;
    }

    public InfNum<BigInteger> GetBoundUpper(NamedInt v) {
        if (!IntBounds.TryGetValue(v, out var bounds))
            return InfNum<BigInteger>.PosInfNum;
        return bounds.Max;
    }

    void WatchVarBound(NamedInt v) {
        NonTermSet nonTermSet = new();
        v.CollectSymbols(nonTermSet, []);
        foreach (var var in nonTermSet.StrVars) {
            if (!VarBoundWatcher.TryGetValue(var, out var watched))
                VarBoundWatcher.Add(var, watched = []);
            watched.Add(v);
        }
    }

    public SimplifyResult AddLowerIntBound(NamedInt v, InfNum<BigInteger> val) {
        Debug.Assert(val != InfNum<BigInteger>.PosInfNum);
        val = InfNum<BigInteger>.Max(val, v.MinLen);
        Interval<BigInteger> i;
        if (val == v.MinLen)
            // Not very helpful
            return SimplifyResult.Proceed;
        if (!IntBounds.TryGetValue(v, out var bounds)) {
            WatchVarBound(v);
            i = new Interval<BigInteger>(val, InfNum<BigInteger>.PosInfNum);
            IntBounds.Add(v, i);
            //AssertToZ3(i.ToZ3Constraint(v, Graph));
            return SimplifyResult.Restart;
        }
        if (val > bounds.Max)
            return SimplifyResult.Conflict;
        if (val <= bounds.Min)
            return SimplifyResult.Proceed;
        i = new Interval<BigInteger>(val, bounds.Max);
        IntBounds[v] = i;
        //AssertToZ3(i.ToZ3Constraint(v, Graph));
        return SimplifyResult.Restart;
    }

    public SimplifyResult AddHigherIntBound(NamedInt v, InfNum<BigInteger> val) {
        Debug.Assert(val != InfNum<BigInteger>.NegInfNum);
        if (val < v.MinLen)
            return SimplifyResult.Conflict;
        if (val.IsPosInf)
            // Not very helpful
            return SimplifyResult.Proceed;
        Interval<BigInteger> i;
        if (!IntBounds.TryGetValue(v, out var bounds)) {
            WatchVarBound(v);
            i = new Interval<BigInteger>(v is LenVar ? InfNum<BigInteger>.Zero : InfNum<BigInteger>.NegInfNum, val);
            IntBounds.Add(v, i);
            //AssertToZ3(i.ToZ3Constraint(v, Graph));
            return SimplifyResult.Restart;
        }
        if (val < bounds.Min)
            return SimplifyResult.Conflict;
        if (val >= bounds.Max)
            return SimplifyResult.Proceed;
        i = new Interval<BigInteger>(bounds.Min, val);
        IntBounds[v] = i;
        //AssertToZ3(i.ToZ3Constraint(v, Graph));
        return SimplifyResult.Restart;
    }

    public bool ConsistentIntVal(IntVar var, InfNum<BigInteger> v) =>
        !IntBounds.TryGetValue(var, out var bounds) || bounds.Contains(v);

    // lhs == rhs
    // No need to copy anything!
    public bool IsEq(PDD<BigInteger> lhs, PDD<BigInteger> rhs) {
        IntEq eq = new(lhs, rhs);
        return eq.Simplify(this) switch {
            SimplifyResult.Satisfied => true,
            SimplifyResult.Conflict => false,
            _ => ConstraintsIntEq.Contains(eq),
        };
    }

    // p == 0 || p <= 0 [for implementation syntactic reasons, p == 0 can be true and p <= 0 can be false]
    // No need to copy anything!
    public bool IsPowerElim(PDD<BigInteger> p) => IsZero(p) || IsNonPos(p);

    // p == 0
    // No need to copy anything!
    public bool IsZero(PDD<BigInteger> p) => IsEq(p, Env.ZeroInt);

    // p == 1
    // No need to copy anything!
    public bool IsOne(PDD<BigInteger> p) => IsEq(p, Env.OneInt);

    // lhs <= rhs
    // lhs - rhs <= 0
    // No need to copy anything!
    public bool IsLe(PDD<BigInteger> lhs, PDD<BigInteger> rhs) {
        IntLe le = IntLe.MkLe(lhs, rhs);
        return le.Simplify(this) switch {
            SimplifyResult.Satisfied => true,
            SimplifyResult.Conflict => false,
            _ => ConstraintsIntLe.Contains(le),
        };
    }

    // lhs < rhs
    // lhs - rhs < 0
    // lhs - rhs < 0
    // lhs - rhs + 1 <= 0
    // No need to copy anything!
    public bool IsLt(PDD<BigInteger> lhs, PDD<BigInteger> rhs) {
        IntLe le = IntLe.MkLt(lhs, rhs);
        return le.Simplify(this) switch {
            SimplifyResult.Satisfied => true,
            SimplifyResult.Conflict => false,
            _ => ConstraintsIntLe.Contains(le),
        };
    }

    // p < 0
    // No need to copy anything!
    public bool IsNeg(PDD<BigInteger> p) => IsLt(p, Env.ZeroInt);

    // p <= 0
    // No need to copy anything!
    public bool IsNonPos(PDD<BigInteger> p) => IsLe(p, Env.ZeroInt);

    // p > 0
    // No need to copy anything!
    public bool IsPos(PDD<BigInteger> p) => IsLt(Env.ZeroInt, p);

    // p >= 0
    // No need to copy anything!
    public bool IsNonNeg(PDD<BigInteger> p) => IsLe(Env.ZeroInt, p);

#if false
    // Just express one variable in each equation and substitute it everywhere
    Dictionary<NamedInt, PDD<BigRational>> ResolveIntEqs() {
        List<PDD<BigRational>> expressed = [];
        Dictionary<NamedInt, int> eliminated = [];

        foreach (var eq in ConstraintsIntEq) {
            HashSet<NamedInt> nonLinear = [];
            Dictionary<NamedInt, BigInteger> linear = [];
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

            if (linear.Count == 0)
                continue;
            (NamedInt bestVar, BigInteger bestCoeff) = linear.First();
            bestCoeff = BigInteger.Abs(bestCoeff);
            foreach (var l in linear) {
                var cr = BigInteger.Abs(l.Value);
                if (cr >= bestCoeff)
                    continue;
                bestVar = l.Key;
                bestCoeff = cr;
            }
            Debug.Assert(!bestCoeff.IsZero);
            Debug.Assert(!eliminated.ContainsKey(bestVar));

            var def = eq.Poly.ToRatPoly();
            def.Sub(new BigRational(bestCoeff), new StrictMonomial(bestVar));
            def = def.Div(new BigRational(bestCoeff));
            for (int j = 0; j < expressed.Count; j++) {
                var e = expressed[j];
                expressed[j] = e.Apply(bestVar, def);
            }
            eliminated.Add(bestVar, expressed.Count);
            expressed.Add(def);
        }
        Dictionary<NamedInt, PDD<BigRational>> result = [];
        foreach (var (v, i) in eliminated) {
            result.Add(v, expressed[i]);
        }
        return result;
    }
#endif

    public IEnumerable<NielsenEdge> Extend(LocalInfo info) {
        Debug.Assert(!IsExtended);
        // get minimal split
        Debug.Assert(ConstraintsStrEq.Count > 0 || ConstraintsStrMem.Count > 0);
        Debug.Assert(Outgoing.Count == 0);
        ModifierBase? bestModifier = null;

        //Dictionary<NamedInt, PDD<BigRational>> intSubst = ResolveIntEqs();

        foreach (var cnstr in ConstraintsStrEq) {
            ModifierBase? currentModifier = cnstr.Extend(this, []);
            if (currentModifier is null)
                continue;
            if (bestModifier is null || currentModifier.CompareTo(bestModifier) < 0)
                bestModifier = currentModifier;
        }
        foreach (var cnstr in ConstraintsStrMem) {
            ModifierBase? currentModifier = cnstr.Value.Extend(this, []);
            if (currentModifier is null)
                continue;
            if (bestModifier is null || currentModifier.CompareTo(bestModifier) < 0)
                bestModifier = currentModifier;
        }
#if false
        foreach (var cnstr in ConstraintsReSplit) {
            ModifierBase currentModifier = cnstr.Extend(this, []);
            if (bestModifier is null || currentModifier.CompareTo(bestModifier) < 0)
                bestModifier = currentModifier;
        }
#endif
        Debug.Assert(bestModifier is not null);
        foreach (var child in bestModifier.Apply(info)) {
            int modCnt = info.ModCnt;
            child.IncModCount(info);
            SimplifyAndInit(info, child);
            child.DecModCount(info);
            Debug.Assert(modCnt == info.ModCnt);
            yield return child;
        }
        IsExtended = true;
    }

    static int simplifyChainCnt;

    public static BacktrackReasons SimplifyAndInit(LocalInfo info, NielsenEdge? edge) {
        // we need to track the last edge to change the target on subsumption
        Debug.Assert(edge is null || ReferenceEquals(info.CurrentNode, edge.Tgt));
        if (info.CurrentNode.IsCurrentlyConflict)
            return info.CurrentNode.CurrentReason;
        bool force = edge is null;

        List<NielsenEdge> edgeChain = [];
        simplifyChainCnt++;

        void Fail() {
            for (var i = edgeChain.Count; i > 0; i--) {
                // Inherit reason for only child
                Debug.Assert(edgeChain[i - 1].Src.Outgoing.Count == 1);
                edgeChain[i - 1].Src.CurrentReason = BacktrackReasons.ChildrenFailed;
                edgeChain[i - 1].DecModCount(info);
            }
        }

        while (true) {
            if (info.CurrentNode.Graph.OuterPropagator.Cancel)
                throw new SolverTimeoutException();
            info.CurrentNode.evalIdx = info.CurrentNode.Graph.RunIdx;

            NonTermSet modSet = new();
            DetModifier outSideCnstr = new();
            var reason = info.CurrentNode.Simplify(info, modSet, outSideCnstr, force);
            if (reason is not BacktrackReasons.Unevaluated) {
                info.CurrentNode.IsGeneralConflict = true;
                info.CurrentNode.CurrentReason = reason;
                Fail();
                return reason;
            }

            if (outSideCnstr.Trivial) {
#if true
                // subsumption check
                // TODO: Optimize
                // var existing = node.Graph.FindExisting(node);
                // if (edge is not null && existing is not null) {
                //     edge.Tgt = existing; // Take the existing node
                //     // Hard to delete the existing node so let's keep it pending...
                //     Debug.Assert(node.Outgoing.IsEmpty());
                //     node.evalIdx = 0;
                //     Debug.Assert(edge.Src.IsExtended);
                // }
#endif

                for (var i = edgeChain.Count; i > 0; i--) {
                    edgeChain[i - 1].DecModCount(info);
                }
                return BacktrackReasons.Unevaluated;

            }
            // not subsumed, so we need to keep the node
            // node.Graph.PersistPending();
            Debug.Assert(info.CurrentNode.Outgoing.Count == 0);

            int cnt = 0;
            foreach (var _ in outSideCnstr.Apply(info)) {
                cnt++;
            }
            info.CurrentNode.IsExtended = true;
            Debug.Assert(info.CurrentNode.Outgoing.Count == 1 && cnt == 1);

            edge = info.CurrentNode.Outgoing[0];

            edge.IncModCount(info);
            edgeChain.Add(edge);
        }
    }

    public void CollectSymbols(NonTermSet nonTermSet, CharacterSet alphabet) {
        foreach (var cnstr in ConstraintsStrEq) {
            cnstr.CollectSymbols(nonTermSet, alphabet);
        }
        foreach (var cnstr in ConstraintsStrMem) {
            cnstr.Value.CollectSymbols(nonTermSet, alphabet);
        }
    }

    static int simplifyCnt;

    public BacktrackReasons Simplify(LocalInfo info, NonTermSet modSet, DetModifier outSideCnstr,
        bool forceRewriteAll) {
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
                switch (c.SimplifyAndPropagate(info, modSet, outSideCnstr, ref reason)) {
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
                if (!outSideCnstr.Trivial)
                    break;
            }
            if (!outSideCnstr.Trivial)
                // Better we integrate the new information 
                // otw., x...x = cxa...axc could give x / cx and x / xc but this "c" might be the same one
                // so either try to unify the substitutions, or just apply every substitution as soon as we get it
                break;
        }
        propagate:

        Dictionary<NamedStrToken, Dictionary<NamedStrToken, uint>>
            largerVars = []; // if |x| = |y| + d + ... then x > y [strictly!]
        Dictionary<NamedStrToken, uint> lowerBounds = []; // if d <= |x| with x > 0

        // TODO: Do this also for inequalities
        // foreach (var eq in IntEq) {
        //     // collect |x| == |y| + d + ... then x <= y
        //     if (!eq.GetLess(largerVars))
        //         return BacktrackReasons.Arithmetic;
        // }
        // foreach (var bound in IntBounds) {
        //     Debug.Assert(!bound.Value.Min.IsPosInf);
        //     if (bound is { Key: LenVar lv, Value.Min.IsPos: true })
        //         lowerBounds.Add(lv.Var, (uint)(BigInteger)bound.Value.Min);
        // }

        foreach (var eq in ConstraintsStrEq) {
            if (eq.Satisfied)
                continue;
            eq.GetNielsenDep(Graph.Env, forwardVarDep, true);
            eq.GetNielsenDep(Graph.Env, backwardVarDep, false);
        }
        foreach (var eq in ConstraintsStrEq) {
            if (eq.Satisfied)
                continue;
            eq.SimplifyUnitNielsen(Env, outSideCnstr, forwardVarDep, largerVars, lowerBounds, true);
            eq.SimplifyUnitNielsen(Env, outSideCnstr, backwardVarDep, largerVars, lowerBounds, false);
        }
        Normalize();
        foreach (var c in toRemove) {
            RemoveConstraint(c);
        }
        return BacktrackReasons.Unevaluated;
    }

    void Normalize() {
        // TODO: Eliminate duplicates
        ConstraintsStrEq.Sort();
        // ConstraintsStrMem.Sort();
        // ConstraintsReSplit.Sort(); -- no real reason to sort it...
        ConstraintsIntEq.Sort();
        ConstraintsIntLe.Sort();
    }

    public void RemoveConstraint(Constraint cnstr) {
        switch (cnstr) {
            case StrEq sEq:
                RemoveStrEq(sEq);
                break;
            case StrMem sMem:
                RemoveStrMem(sMem);
                break;
            /*case ReSplit rSplit:
                RemoveReSplit(rSplit);
                break;*/
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
        Debug.Assert(ConstraintsStrEq.SkipLast(ConstraintsStrEq.Count - 1).Zip(
                ConstraintsStrEq.Skip(1)
            ).All(o => o.First.CompareTo(o.Second) <= 0)
        );
        Log.Verify(ConstraintsStrEq.Remove(toRemove));
        while (ConstraintsStrEq.Remove(toRemove)) { }
    }

    public void RemoveStrMem(StrMem toRemove) =>
        Log.Verify(ConstraintsStrMem.Remove(toRemove.Id));

    /*public void RemoveReSplit(ReSplit toRemove) {
        // The set can contain the same element multiple times after simplification (unfortunately)
        Debug.Assert(ConstraintsReSplit.SkipLast(ConstraintsReSplit.Count - 1).Zip(
                ConstraintsReSplit.Skip(1)
            ).All(o => o.First.CompareTo(o.Second) <= 0)
        );
        Log.Verify(ConstraintsReSplit.Remove(toRemove));
        while (ConstraintsReSplit.Remove(toRemove)) {}
    }*/

    public void RemoveIntEq(IntEq toRemove) {
        Debug.Assert(ConstraintsIntEq.SkipLast(ConstraintsStrEq.Count - 1).Zip(
                ConstraintsIntEq.Skip(1)
            ).All(o => o.First.CompareTo(o.Second) <= 0)
        );
        Log.Verify(ConstraintsIntEq.Remove(toRemove));
        while (ConstraintsIntEq.Remove(toRemove)) { }
    }

    public void RemoveIntLe(IntLe toRemove) {
        Debug.Assert(ConstraintsIntLe.SkipLast(ConstraintsStrEq.Count - 1).Zip(
                ConstraintsIntLe.Skip(1)
            ).All(o => o.First.CompareTo(o.Second) <= 0)
        );
        Log.Verify(ConstraintsIntLe.Remove(toRemove));
        while (ConstraintsIntLe.Remove(toRemove)) { }
    }

    public NielsenNode MkChild(LocalInfo info,
        IReadOnlyList<Subst> subst,
        IReadOnlyList<CharSubst> substC,
        IReadOnlyCollection<Constraint> sideConds,
        IReadOnlyCollection<Constraint> toRemove, bool progress) {

        var child = new NielsenNode(info, subst, substC, sideConds, progress);
        foreach (var c in toRemove) {
            child.RemoveConstraint(c);
        }
        // First apply the substitutions
        foreach (var s in subst) {
            child.Apply(s, child);
        }
        foreach (var s in substC) {
            child.Apply(s, child);
        }
        // ... then add the new stuff
        foreach (var cond in sideConds) {
            child.AddConstraint(cond);
        }
        return child;
    }

    public NielsenNode Clone() =>
        new(Graph, this);

    public List<(Constraint orig, Constraint simpl)> CheckModel(Interpretation itp) {
        List<(Constraint, Constraint)> unsatisfied = [];
        NielsenNode dummyNode = new NielsenNode(Graph);
        foreach (var orig in AllConstraints) {
            var cnstr = orig.Apply(itp);
            BacktrackReasons reason = BacktrackReasons.Unevaluated;
            if (cnstr.SimplifyAndPropagate(new LocalInfo(dummyNode), new NonTermSet(), new DetModifier(), ref reason) ==
                SimplifyResult.Satisfied)
                continue;
            unsatisfied.Add((orig, cnstr));
        }
        return unsatisfied;
    }

    public override bool Equals(object? obj) {
        if (obj is not NielsenNode other)
            return false;
        return Id == other.Id && ReferenceEquals(Graph, other.Graph);
    }

    public bool EqualContent(NielsenNode other) {
        if (ReferenceEquals(this, other))
            return true;
        if (ConstraintsStrEq.Count != other.ConstraintsStrEq.Count ||
            ConstraintsStrMem.Count != other.ConstraintsStrMem.Count ||
            //ConstraintsReSplit.Count != other.ConstraintsReSplit.Count ||
            IntBounds.Count != other.IntBounds.Count)
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

    // We deliberately only check for the constraints and not the bounds/diseqs (we can do this later on the semantic check)
    // This function is not in sync with Equals(object?), but this is not super important!!
    public override int GetHashCode() =>
        AllConstraints.Aggregate(164304773, (i, v) => i + 366005033 * v.GetHashCode());

    public bool AddConstraint(Constraint cnstr) {
        switch (cnstr) {
            case StrEq sEq:
                return ConstraintsStrEq.Add(sEq);
            case StrMem sMem:
                ConstraintsStrMem.Add(sMem.Id, sMem);
                return true;
            case IntEq iEq:
                return ConstraintsIntEq.Add(iEq);
            case IntLe iLe:
                return ConstraintsIntLe.Add(iLe);
            default:
                throw new NotSupportedException();
        }
    }

    public void AddConstraint(SymCharToken o, CharacterSet set) {
        if (!CharRanges.TryGetValue(o, out CharacterSet? value)) {
            CharRanges.Add(o, set);
            return;
        }
        CharRanges[o] = value.IntersectWith(set);
    }

    public bool AddCharConstraints(SymCharToken c, CharacterSet @case) {
        if (!CharRanges.TryGetValue(c, out CharacterSet? value)) {
            CharRanges.Add(c, @case);
            return true;
        }
        var r = value.IntersectWith(@case);
        CharRanges[c] = r;
        return !r.IsEmpty;
    }

    void GcConstraints() {
        // For performance, we can drop everything to regain memory
        ConstraintsStrEq.Clear();
        ConstraintsStrMem.Clear();
        //ConstraintsReSplit.Clear();
        ConstraintsIntEq.Clear();
        ConstraintsIntLe.Clear();
        DisEqualities.Clear();
        CharRanges.Clear();
        IntBounds.Clear();
        VarBoundWatcher.Clear();
        forwardVarDep.Clear();
        backwardVarDep.Clear();
    }

    // Checks if stronger is more constrained than this
    public bool Subsumes(NielsenNode stronger) {
        Debug.Assert(stronger.ConstraintsStrEq.Equals(ConstraintsStrEq));
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
            BacktrackReasons.Subsumption or
            BacktrackReasons.Arithmetic or
            BacktrackReasons.Regex or
            BacktrackReasons.RegexWidening or
            BacktrackReasons.CharacterRange or
            BacktrackReasons.SMT or
            BacktrackReasons.ChildrenFailed;

    public static bool IsActualConflict(BacktrackReasons reason) =>
        IsConflictReason(reason) && reason != BacktrackReasons.ChildrenFailed;

    public static string ReasonToString(BacktrackReasons reason) => reason switch {
        BacktrackReasons.Unevaluated => "Unevaluated",
        BacktrackReasons.SymbolClash => "Symbol Clash",
        BacktrackReasons.ParikhImage => "Parikh Image",
        BacktrackReasons.Arithmetic => "Arithmetic",
        BacktrackReasons.Regex => "Regex",
        BacktrackReasons.RegexWidening => "RegexWidening",
        BacktrackReasons.Subsumption => "Subsumption",
        BacktrackReasons.CharacterRange => "Character Range",
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

    bool IsSkipEdge(NielsenEdge edge, LocalInfo info) {
        if (edge.Tgt.IsGeneralConflict)
            // it is a contradiction independent of the forbidden edges
            return true;
        if (edge.Tgt is { IsActive: true, IsCurrentlyConflict: true })
            // We already marked it conflicting in a previous iterative deepening round
            return true;
        var blocker = edge.Asserted.FirstOrDefault(info.Forbidden.Contains);
        if (blocker is not null) {
            // The outer SMT solver has blocked this path
            // Otw. it might not necessarily be a conflict
            if (edge.Asserted.Any(info.UsedForbidden.Contains))
                // one respective blocker was already added anyway - no reason to add another (keep conflict small)
                return true;
            // otw. just add the found blocker as a new one
            info.UsedForbidden.Add(blocker);
            return true;
        }
        return false;
    }

    static int checkCnt;

    // Unit and progression steps are not countered for depth bound
    public SolveResult Check(int dep, LocalInfo info) {
        Debug.Assert(Graph.RunIdx > 0);

        // We can do this only in case there is no sat node reachable from there
        //if (!info.currentPath.ContainsKey(Id))
        // We found a cycle
        //    return SolveResult.CYCLIC;

        // The node could be from a different run - reset its values
        Activate();

        if (IsCurrentlyConflict)
            return SolveResult.UNSAT;

        checkCnt++;

#if DEBUG
        if (info.CurrentPath.Count > 100)
            Console.WriteLine("Suspiciously deep nesting...");
#endif

        bool delayedPush = false;
        try {
            Debug.Assert(IsActive);

            if (!IsExtended) {
                // TODO: Check Regex intersection

                Status z3Res = Status.UNKNOWN;
                if (IsProgressNode) {
                    // We made progress - let's check if this is already enough to get an integer conflict
                    // This can be expensive, so we only do this in case the formula simplified "strongly" before
                    // => we ask Z3
                    delayedPush = info.DelayedAssert();
                    z3Res = Graph.SubSolver.Check();
                    if (z3Res == Status.UNKNOWN) {
                        if (Graph.SubSolver.ReasonUnknown is "timeout" or "canceled")
                            throw new SolverTimeoutException();
                        throw new Exception("Z3 returned unknown");
                    }

                    if (z3Res == Status.UNSATISFIABLE) {
                        Debug.Assert(Outgoing.Count == 0);
                        CurrentReason = BacktrackReasons.SMT;
                        IsExtended = true;
                        Debug.Assert(IsCurrentlyConflict);
                        return SolveResult.UNSAT;
                    }
                }

                if (ConstraintsStrEq.Count == 0 && ConstraintsStrMem.All(o => o.Value.IsPrimitiveRegex())) {

                    if (ConstraintsStrMem.Count > 0 && !CheckRegex()) {
                        CurrentReason = BacktrackReasons.Regex;
                        IsGeneralConflict = true;
                        IsExtended = true;
                        Debug.Assert(IsCurrentlyConflict);
                        return SolveResult.UNSAT;
                    }
                    // We might have already checked this if it was a progress node
                    // We need a Z3 result so let's ask if we haven't already
                    if (z3Res == Status.UNKNOWN) {
                        Debug.Assert(!IsProgressNode);
                        z3Res = Graph.SubSolver.Check(info.CurrentPath.SelectMany(o => o.Value.Asserted));
                    }
                    if (z3Res == Status.UNKNOWN) {
                        if (!delayedPush)
                            delayedPush = info.DelayedAssert();
                        if (Graph.SubSolver.ReasonUnknown is "timeout" or "canceled")
                            throw new SolverTimeoutException();
                        throw new Exception("Z3 returned unknown");
                    }
                    // If Z3 says unsat, we backtrack
                    if (z3Res == Status.UNSATISFIABLE) {
                        CurrentReason = BacktrackReasons.SMT;
                        IsExtended = true;
                        Debug.Assert(IsCurrentlyConflict);
                        return SolveResult.UNSAT;
                    }
                    // Otw. we found a candidate model
                    // Graph.PersistPending();
                    Debug.Assert(!IsCurrentlyConflict);
                    return SolveResult.SAT;
                }
                if (dep > Graph.DepthBound && !Options.SaturateGraph)
                    return SolveResult.UNKNOWN;
            }

            bool generalConflict = true; // are all children unsat independent of the path?
            bool gotUnknown = false; // did at least one child fail because of some resource limit?

            Debug.Assert(CurrentReason == BacktrackReasons.Unevaluated);
            Debug.Assert(IsActive);
            Debug.Assert(!IsCurrentlyConflict);

            // track changed regexes
            List<(Str regex, uint id, int prevPos)> changedRegexes = [];
            foreach (var r in ConstraintsStrMem) {
                int prev = info.RegexOccurrence.GetValueOrDefault((r.Value.Regex, r.Key), -1);
                if (prev == -1) {
                    changedRegexes.Add((r.Value.Regex, r.Key, -1));
                    info.RegexOccurrence.Add((r.Value.Regex, r.Key), Id);
                    continue;
                }
                Debug.Assert(info.CurrentPath[prev].Src.ConstraintsStrMem.ContainsKey(r.Key));
                if (info.CurrentPath[prev].Src.ConstraintsStrMem[r.Key].History.Length == r.Value.History.Length)
                    continue;
                Debug.Assert(Id >= 0);
                changedRegexes.Add((r.Value.Regex, r.Key, prev));
                info.RegexOccurrence[(r.Value.Regex, r.Key)] = Id;
            }

            // TODO: Set a node contradiction if all of its children are contradictions (no matter if forbidden or not)
            bool isSat = false;
            if (!IsExtended && extensionEnum is null)
                // we might have breaked out early and not generated all possible edges
                extensionEnum = Extend(info).GetEnumerator();

            for (int i = 0; i < Outgoing.Count || (extensionEnum is not null && extensionEnum.MoveNext()); i++) {
                Debug.Assert(i < Outgoing.Count);
                var outgoing = Outgoing[i];
                if (IsSkipEdge(outgoing, info))
                    continue;
                Debug.Assert(outgoing.Tgt.evalIdx <= Graph.RunIdx);
                outgoing.IncModCount(info);

                int modCnt = info.ModCnt;
                // we want to go deep fast if there is no danger of divergence
                int nextDep = outgoing.Tgt.IsProgressNode ? dep : dep + 1;
                switch (outgoing.Tgt.Check(nextDep, info)) {
                    case SolveResult.SAT:
                        isSat = true;
                        if (Options.SaturateGraph)
                            break;
                        return SolveResult.SAT;
                    case SolveResult.UNSAT:
                        generalConflict &= outgoing.Tgt.IsGeneralConflict;
                        break;
                    case SolveResult.CYCLIC:
                        break;
                    case SolveResult.UNKNOWN:
                        gotUnknown = true;
                        break;
                    default:
                    case SolveResult.UNSOUND:
                        throw new Exception("Sub-Call returned unsound");
                }
                Debug.Assert(modCnt == info.ModCnt);
                outgoing.DecModCount(info);
            }
            IsExtended = true;
            if (extensionEnum is not null) {
                extensionEnum.Dispose();
                extensionEnum = null;
            }
            foreach (var c in changedRegexes) {
                if (c.prevPos == -1)
                    Log.Verify(info.RegexOccurrence.Remove((c.regex, c.id)));
                else
                    info.RegexOccurrence[(c.regex, c.id)] = c.prevPos;
            }

            if (isSat) {
                Debug.Assert(Options.SaturateGraph);
                return SolveResult.SAT;
            }

            if (!Options.KeepProof)
                GcConstraints();

            if (gotUnknown) {
                // We hit at lease once a depth-limit
                Debug.Assert(CurrentReason == BacktrackReasons.Unevaluated);
                return SolveResult.UNKNOWN;
            }

            // All children are inconsistent
            Debug.Assert(!IsGeneralConflict || generalConflict);
            IsGeneralConflict = generalConflict; // if all children failed generally, this node also fails generally
            if (Outgoing.Count > 0)
                CurrentReason = BacktrackReasons.ChildrenFailed;
            return SolveResult.UNSAT;
        }
        finally {
            if (delayedPush)
                info.DelayPop();
        }
    }

    public bool CheckRegex() {
        Debug.Assert(ConstraintsStrMem.All(o => o.Value.IsPrimitiveRegex()));
        Dictionary<NamedStrToken, List<Str>> regexList = [];
        foreach (var cnstr in ConstraintsStrMem) {
            NamedStrToken v = (NamedStrToken)cnstr.Value.Str.First;
            if (!regexList.TryGetValue(v, out var s))
                regexList.Add(v, s = []);
            s.Add(cnstr.Value.Regex);
        }
        foreach (var (_, v) in regexList) {
            Debug.Assert(v.Count > 0);
            if (v is [{ BasicRegex: true }])
                // for more complex regex involving complements and intersection we have to check
                continue;
            if (!Intersect(v))
                return false;
        }
        return true;
    }

    public Dictionary<NamedStrToken, List<CharToken>> WitnessRegex() {
        Debug.Assert(ConstraintsStrMem.All(o => o.Value.IsPrimitiveRegex()));
        Dictionary<NamedStrToken, List<Str>> regexList = [];
        foreach (var cnstr in ConstraintsStrMem) {
            NamedStrToken v = (NamedStrToken)cnstr.Value.Str.First;
            if (!regexList.TryGetValue(v, out var s))
                regexList.Add(v, s = []);
            s.Add(cnstr.Value.Regex);
        }
        Dictionary<NamedStrToken, List<CharToken>> witnesses = [];
        foreach (var (x, v) in regexList) {
            Debug.Assert(v.Count > 0);
            List<CharToken> witness = [];
            Log.Verify(Intersect(v, witness));
            witnesses.Add(x, witness);
        }
        return witnesses;
    }

    public bool CheckRegexWidending(Str str, Str regex) {
        // overapproximate s by assuming the intersection of all primitive constraints as the value of the variables
        Dictionary<NamedStrToken, List<Str>> regexList = [];
        // Get the primitive regex
        foreach (var cnstr in ConstraintsStrMem) {
            if (!cnstr.Value.IsPrimitiveRegex())
                continue;
            if (!str.ContainsVar((NamedStrToken)cnstr.Value.Str.First))
                continue;
            NamedStrToken v = (NamedStrToken)cnstr.Value.Str.First;
            if (!regexList.TryGetValue(v, out var s))
                regexList.Add(v, s = []);
            s.Add(cnstr.Value.Regex);
        }
        Str strApprox = str;
        // TODO: Optimise!!!
        foreach (var r in regexList) {
            strApprox = Env.StrManager.Subst(strApprox, r.Key, Env.StrManager.MkIntersection(r.Value));
        }
        foreach (var r in CharRanges) {
            strApprox = Env.StrManager.Subst(Env, strApprox, r.Key, new SetToken(r.Value));
        }
        // just deal with the remaining variables within the derivative function...
        foreach (var r in str.ContainedVars()) {
            if (regexList.ContainsKey(r))
                continue;
            strApprox = Env.StrManager.Subst(strApprox, r, Env.StrManager.AllStr);
        }
        return Intersect([strApprox, regex]);
    }

    bool Intersect(List<Str> regexes, List<CharToken>? witness = null) {
        // or create the automaton
        Debug.Assert(witness is null || witness.Count == 0);
        Dictionary<Str, (CharacterSet by, Str from)?> visited = [];
        Stack<Str> todo = [];
        Str current = Env.StrManager.MkIntersection(regexes);
        if (current.Nullable)
            return true; // witness is null or empty

        todo.Push(current);
        visited.Add(current, null);

        while (todo.Count > 0) {
            current = todo.Pop();
            var first = current.FirstMinTerms();
            foreach (var c in first.ToCharacterSets()) {
                Str d = current.Derivative(Env, c, true);
                if (d.IsFail || !visited.TryAdd(d, (c, current)))
                    continue;
                todo.Push(d);
                if (!d.Nullable)
                    continue;
                if (witness is null)
                    return true;
                Str it = d;
                while (true) {
                    var prev = visited[it];
                    if (!prev.HasValue)
                        break;
                    witness.Add(prev.Value.by.GetSome());
                    it = prev.Value.from;
                }
                witness.Reverse();
                return true;
            }
        }

        return false;
    }

    public override string ToString() {
        StringBuilder sb = new();
        if (AllConstraints.Any()) {
            sb.AppendLine("Cnstr:");
            foreach (var cnstr in AllConstraints) {
                sb.Append('\t').AppendLine(cnstr.ToString());
            }
        }
        if (DisEqualities.IsNonEmpty()) {
            sb.AppendLine("DisEq:");
            foreach (var cnstr in DisEqualities) {
                sb.Append('\t').AppendLine(cnstr.Key + " != {" +
                                           string.Join(", ", cnstr.Value.Select(o => o.ToString())) + "}");
            }
        }
        if (CharRanges.IsNonEmpty()) {
            sb.AppendLine("Ranges:");
            foreach (var cnstr in CharRanges) {
                sb.Append('\t').AppendLine(cnstr.Key + " in " + cnstr.Value);
            }
        }
        if (IntBounds.IsNonEmpty()) {
            sb.AppendLine("Bounds:");
            foreach (var (v, i) in IntBounds) {
                sb.Append('\t').Append(i.Min).Append(" \u2264 ").Append(v).Append(" \u2264 ")
                    .AppendLine(i.Max.ToString());
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
        if (DisEqualities.IsNonEmpty()) {
            sb.Append("DisEq:\\n");
            foreach (var cnstr in DisEqualities) {
                sb.Append('\t').Append(cnstr.Key + " &ne; {" +
                                           string.Join(", ", cnstr.Value.Select(o => DotEscapeStr(o.ToString()))) + "}").Append("\\n");
            }
        }
        if (CharRanges.IsNonEmpty()) {
            sb.Append("Ranges:\\n");
            foreach (var cnstr in CharRanges) {
                sb.Append('\t').Append(DotEscapeStr(cnstr.Key.ToString()) + " &isin; " + DotEscapeStr(cnstr.Value.ToString())).Append("\\n");
            }
        }
        if (IntBounds.Count > 0) {
            sb.Append("Bounds:\\n");
            foreach (var (v, i) in IntBounds) {
                sb.Append(i.Min).Append(" \u2264 ").Append(DotEscapeStr(v.ToString())).Append(" \u2264 ").Append(i.Max)
                    .Append("\\n");
            }
        }
        return sb.Length == 0 ? "\u22a4" : sb.ToString();
    }
}