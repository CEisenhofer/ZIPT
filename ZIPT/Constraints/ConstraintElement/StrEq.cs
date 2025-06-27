using System.Diagnostics;
using System.Numerics;
using Microsoft.Z3;
using ZIPT.Constraints.ConstraintElement.AuxConstraints;
using ZIPT.Constraints.Modifier;
using ZIPT.IntUtils;
using ZIPT.MiscUtils;
using ZIPT.Tokens;

namespace ZIPT.Constraints.ConstraintElement;

public sealed class StrEq : StrEqBase {

    public StrEq(Str lhs, Str rhs, NonTermSet dependencies) : base(lhs, rhs, dependencies) { }
    public StrEq(Str lhs, Str rhs) : base(lhs, rhs, Str.CollectSymbols(lhs, rhs)) { }
    public StrEq(Str empty, NonTermSet dependencies) : base([], empty, dependencies) { }
    public StrEq(Str empty) : base([], empty, Str.CollectSymbols(empty)) { }

    public override StrEq Clone() => 
        new(LHS.Clone(), RHS.Clone(), Dependencies.Clone());

    public void GetNielsenDep(Dictionary<NamedStrToken, Dictionary<NamedStrToken, Str>> varDep, bool dir) {
        if (LHS.IsEmpty() || RHS.IsEmpty())
            return;
        var s1 = LHS;
        var s2 = RHS;
        var t1 = s1.Peek(dir);
        var t2 = s2.Peek(dir);
        if (t2 is NamedStrToken) {
            (s1, s2) = (s2, s1);
            (t1, t2) = (t2, t1);
        }
        if (t1 is not NamedStrToken v1)
            return;
        if (t2 is NamedStrToken v2) {
            Debug.Assert(!v1.Equals(v2));
            if (!varDep.TryGetValue(v1, out Dictionary<NamedStrToken, Str>? varSet))
                varDep.Add(v1, varSet = []);
            varSet[v2] = [];
            if (!varDep.TryGetValue(v2, out varSet))
                varDep.Add(v2, varSet = []);
            varSet[v1] = [];
            return;
        }
        Str s = [];
        for (int i = 0; i < s2.Count; i++) {
            var t = s2.Peek(dir, i);
            if (t is NamedStrToken v3) {
                if (!varDep.TryGetValue(v1, out Dictionary<NamedStrToken, Str>? varSet))
                    varDep.Add(v1, varSet = []);
                if (varSet.TryGetValue(v3, out Str? old)) {
                    if (old.Count <= s.Count)
                        return;
                    varSet[v3] = old;
                    return;
                }
                varSet.Add(v3, s);
                return;
            }
            s.Add(t, !dir);
        }
    }

    static bool HasDepCycle(NamedStrToken x, NamedStrToken to, Dictionary<NamedStrToken, Dictionary<NamedStrToken, Str>> varDep, HashSet<NamedStrToken> visited, List<(NamedStrToken v, Str prefix)> path) {
        if (x.Equals(to))
            return true;
        if (!visited.Add(x))
            return false;
        if (!varDep.TryGetValue(x, out var dep)) {
            visited.Remove(x);
            return false;
        }
        if (dep.TryGetValue(to, out var r)) {
            path.Add((x, r));
            return true;
        }
        foreach (var (v, s) in dep) {
            if (!HasDepCycle(v, to, varDep, visited, path))
                continue;
            path.Add((x, s));
            return true;
        }
        visited.Remove(x);
        return false;
    }

    public void SimplifyUnitNielsen(DetModifier sConstr,
        Dictionary<NamedStrToken, Dictionary<NamedStrToken, Str>> varDep,
        Dictionary<NamedStrToken, Dictionary<NamedStrToken, uint>> largerVars,
        Dictionary<NamedStrToken, uint> lowerBounds, bool dir) {

        SortStr();
        if (LHS.IsEmpty())
            return;

        Str s1 = LHS;
        Str s2 = RHS;
        StrToken t1 = s1.Peek(dir);
        StrToken t2 = s2.Peek(dir);

        if (t2 is NamedStrToken) {
            (s1, s2) = (s2, s1);
            (t1, t2) = (t2, t1);
        }
        // if there is a variable then there is one at position 1
        if (t1 is not NamedStrToken v1) 
            return;

        // check unit cases by lengths
        Str s = [];
        int i;
        if (lowerBounds.TryGetValue(v1, out uint lowerBound) |
            largerVars.TryGetValue(v1, out Dictionary<NamedStrToken, uint>? larger)) {

            for (i = 0; i < s2.Count; i++) {
                t2 = s2.Peek(dir, i);
                if (lowerBound > 0 && t2 is UnitToken u2) {
                    lowerBound--;
                    s.Add(u2, !dir);
                    continue;
                }
                if (larger is not null && t2 is NamedStrToken v2 && larger.TryGetValue(v2, out uint val)) {
                    Debug.Assert(val > 0);
                    val--;
                    if (val == 0)
                        larger.Remove(v2);
                    else
                        larger[v2] = val;
                    s.Add(v2, !dir);
                    continue;
                }
                break;
            }
            if (s.IsNonEmpty()) {
                if (lowerBound == 0)
                    lowerBounds.Remove(v1);
                else
                    lowerBounds[v1] = lowerBound;
            }
        }
        // TODO: Check the other if it is also a variable

        if (s.IsNonEmpty()) {
            sConstr.Add(new SubstVar(v1, s));
        }

        if (t2 is not CharToken || s1.Count <= 1)
            return;

        // check unit cases by look-ahead
        Debug.Assert(s2.IsNonEmpty());

        // uyw = xvw' and u, v ground and x does not depend on y (otw. we would result in an infinite sequence of unit propagations if it is unsat)
        // x / u' x with u' <= u while u' incompatible with v and u' is char only
        i = 0;
        for (; i < s2.Count && s2.Peek(dir, i) is CharToken; i++) {
            // TODO: Use consistent prefix (requires some resource improvements first though)
            int j1 = 1;
            int j2 = i;
            bool failed = false;
            while (j1 < s1.Count && j2 < s2.Count) {
                StrToken st1 = s1.Peek(dir, j1);
                StrToken st2 = s2.Peek(dir, j2);
                if (st2 is not CharToken stc2)
                    // We cannot say - abort
                    break;
                if (st1 is not CharToken && !st1.Equals(v1))
                    // If we have something like ayu = xbxbv (i.e., x again) we can just assume the copied values so far [0...i)
                    // so we can proceed
                    break;
                if (st1 is CharToken stc1) {
                    // This is the simple case
                    if (stc1.Equals(stc2)) {
                        j1++;
                        j2++;
                        continue;
                    }
                    failed = true;
                    break;
                }
                Debug.Assert(st1 is NamedStrToken);
                bool incomparable = false;
                // We need to compare to the already copied values
                for (int l = 0; j2 < s2.Count && l < i; l++) {
                    st2 = s2.Peek(dir, j2);
                    if (st2 is not CharToken) {
                        incomparable = true;
                        // We cannot say - abort
                        break;
                    }
                    Debug.Assert(s2.Peek(dir, l) is CharToken);
                    if (st2.Equals(s2.Peek(dir, l))) {
                        j2++;
                        continue;
                    }
                    failed = true;
                    break;
                }
                if (incomparable || failed)
                    break;
                j1++;
            }
            if (failed)
                // The prefix is inconsistent - we can proceed
                continue;
            break;
        }
        if (i <= 0)
            return;
        // i == 0 => nothing to do.

        // Check if the next variable is not the variable that depends on the initial one ("unwinding" this way would not necessarily terminate)
        // => Use power instead
        int k = i;
        StrToken? t;
        for (; k < s2.Count; k++) {
            t = s2.Peek(dir, k);
            if (t is NamedStrToken/* or PowerToken*/)
                break;
        }
        if (k < s2.Count) {
            t = s2.Peek(dir, k);
            Debug.Assert(t is not null);
            if (/*t is PowerToken || */HasDepCycle((NamedStrToken)t, v1, varDep, [], []))
                // We also skip powers, as e.g., xy a^n a = yx b z would add infinitely many F / Fa because 
                // length constraint |y| + |x| + n + 1 = |x| + |y| + 1 + |z| would just make n bigger, making a^n unwinding once more
                return;
        }
        s = new Str(i + 1);
        for (int j = 0; j < i; j++) {
            s.Add(s2.Peek(dir, j), !dir);
        }
        s.Add(v1, !dir);
        sConstr.Add(new SubstVar(v1, s));
    }

    static SimplifyResult SimplifyEmpty(IEnumerable<StrToken> s, NielsenNode node, DetModifier sConstr) {
        foreach (var t in s) {
            if (t is UnitToken)
                return SimplifyResult.Conflict;
            if (t is StrVarToken v)
                return sConstr.Add(new SubstVar(v));
            if (t is PowerToken p) {
                if (node.IsLt(new IntPoly(), p.Power))
                    // p.Power > 0
                    sConstr.Add(new StrEq(p.Base));
                else if (!p.Base.IsNullable(node))
                    // p.Base != ""
                    sConstr.Add(new IntEq(p.Power));
            }
            else
                throw new NotSupportedException();
        }
        return SimplifyResult.Proceed;
    }

    // Try to add the substitution: x / s ==> do an occurrence check. If it fails, we have to add it as an ordinary equation
    public SimplifyResult AddDefinition(StrVarToken v, Str s, NielsenNode node, DetModifier sConstr) {
        if (s.RecursiveIn(v))
            // newSideConstr.Add(new StrEq([v], s));
            return SimplifyResult.Proceed;
        return sConstr.Add(new SubstVar(v, s));
    }

    SimplifyResult SimplifyDir(NielsenNode node, DetModifier sConstr, bool dir) {
        // This can cause problems, as it might unwind/compress the beginning/end over and over again (might even detect it as subsumed)
        var s1 = LHS;
        var s2 = RHS;
        SortStr(ref s1, ref s2, dir);
        while (LHS.IsNonEmpty() && RHS.IsNonEmpty()) {
            SortStr(ref s1, ref s2, dir);
            Debug.Assert(s1.Count > 0);
            Debug.Assert(s2.Count > 0);

            if (SimplifySame(s1, s2, dir))
                continue;

            var t1 = s1.Peek(dir);
            var t2 = s2.Peek(dir);

            if (t1 is UnitToken u1 && t2 is UnitToken u2 && node.AreDiseq(u1, u2))
                return SimplifyResult.Conflict;

            if (t1 is SymCharToken sc1 && t2 is UnitToken u)
                return sConstr.Add(new SubstSChar(sc1, u));

            if (t1 is PowerToken p1) {
                if (node.IsZero(p1.Power)) {
                    s1.Drop(dir);
                    continue;
                }
                if (!IsPrefixConsistent(node, p1.Base, s2, dir)) {
                    sConstr.Add(new IntEq(new IntPoly(), p1.Power));
                    return SimplifyResult.Proceed;
                }
            }
            if (t2 is PowerToken p2) {
                if (node.IsZero(p2.Power)) {
                    s2.Drop(dir);
                    continue;
                }
                if (!IsPrefixConsistent(node, p2.Base, s1, dir)) {
                    sConstr.Add(new IntEq(new IntPoly(), p2.Power));
                    return SimplifyResult.Proceed;
                }
            }

            if (SimplifyPower(node, s1, s2, dir))
                continue;
            break;
        }
        return SimplifyResult.Proceed;
    }

    static int simplifyCount;

    protected override SimplifyResult SimplifyAndPropagateInternal(NielsenNode node, DetModifier sConstr, ref BacktrackReasons reason) {
        simplifyCount++;
        Log.WriteLine($"Simplify Eq ({simplifyCount}): {LHS} = {RHS}");
        LHS = LcpCompression(LHS) ?? LHS;
        RHS = LcpCompression(RHS) ?? RHS;
        if (SimplifyDir(node, sConstr, true) == SimplifyResult.Conflict) {
            reason = BacktrackReasons.SymbolClash;
            return SimplifyResult.Conflict;
        }

        if (SimplifyDir(node, sConstr, false) == SimplifyResult.Conflict) {
            reason = BacktrackReasons.SymbolClash;
            return SimplifyResult.Conflict;
        }

        if (LHS.IsEmpty() && RHS.IsEmpty())
            return SimplifyResult.Satisfied;

        if (LHS.IsEmpty() || RHS.IsEmpty()) {
            var eq = LHS.IsEmpty() ? RHS : LHS;
            // Remove powers that actually do not exist anymore
            while (eq.IsNonEmpty() && eq.Peek(true) is PowerToken p) {
                Str? s;
                if ((s = SimplifyPowerSingle(node, p)) is not null) {
                    eq.Drop(true);
                    eq.AddRange(s, true);
                    continue;
                }
                break;
            }
            if (eq.IsEmpty())
                return SimplifyResult.Satisfied;
            if (SimplifyEmpty(eq, node, sConstr) == SimplifyResult.Conflict) {
                reason = BacktrackReasons.SymbolClash;
                return SimplifyResult.Conflict;
            }
            SortStr();
            return SimplifyResult.Proceed;
        }

        // Check Multiset abstraction
        var lhsSet = LHS.ToSet();
        var rhsSet = RHS.ToSet();
        MSet<StrToken, BigInt>.ElimCommon(lhsSet, rhsSet);
        if (lhsSet.IsEmpty() != rhsSet.IsEmpty()) {
            var nonEmpty = lhsSet.IsEmpty() ? rhsSet : lhsSet;
            // Remove powers that actually do not exist anymore
            while (nonEmpty.IsNonEmpty() && nonEmpty.First().t is PowerToken p) {
                Str? s;
                if ((s = SimplifyPowerSingle(node, p)) is not null) {
                    nonEmpty.RemoveAll(p);
                    nonEmpty.Add(s);
                    continue;
                }
                break;
            }
            if (SimplifyEmpty(nonEmpty.Keys, node, sConstr) == SimplifyResult.Conflict) {
                reason = BacktrackReasons.ParikhImage;
                return SimplifyResult.Conflict;
            }
            SortStr();
            return SimplifyResult.Proceed;
        }
        /*if (lhsSet.IsNonEmpty() && rhsSet.IsNonEmpty()) {
            if (lhsSet.All(o => o.t is CharToken) &&
                rhsSet.All(o => o.t is CharToken)) {
                reason = BacktrackReasons.ParikhImage;
                return SimplifyResult.Conflict;
            }
            if (CheckMultiSequenceParikh(LHS, RHS)) {
                reason = BacktrackReasons.ParikhImage;
                return SimplifyResult.Conflict;
            }
        }*/
        // Propagate assignments

        if (LHS is [StrVarToken] || RHS is [StrVarToken]) {
            var (v, s) = LHS is [StrVarToken] ? ((StrVarToken)LHS[0], RHS) : ((StrVarToken)RHS[0], LHS);
            // important: clone it; otherwise one might into endless recursions when applied to itself
            AddDefinition(v, s, node, sConstr);
        }
        SortStr();
        return SimplifyResult.Proceed;
    }

    NumCmpModifier? SplitPowerElim(StrToken t, Str s, bool dir) {
        if (t is not PowerToken p1)
            return null;
        var r = CommPower(p1.Base, s, dir);
        return r.idx > 0 ? new NumCmpModifier(p1.Power, r.num) : null;
    }

    NumUnwindingModifier? SplitPowerUnwind(StrToken t, bool varInvolved) => 
        t is not PowerToken p ? null : (varInvolved ? new VarNumUnwindingModifier(p.Power) : new ConstNumUnwindingModifier(p.Power));

    List<(NamedStrToken x, Str val)> TryGetPowerSplitBase(StrVarToken v, Str s, Dictionary<NamedStrToken, Dictionary<NamedStrToken, Str>> varDep, bool dir) {
        if (s.IsEmpty())
            return [];
        Str p = [];
        var i = 0;
        for (; i < s.Count && s.Peek(dir, i) is not NamedStrToken; i++) {
            p.Add(s.Peek(dir, i), !dir);
        }

        if (i >= s.Count)
            // Non-rec Case
            return [];
        var x = (NamedStrToken)s.Peek(dir, i);
        List<(NamedStrToken v, Str prefix)> path = [];

        if (!HasDepCycle(x, v, varDep, [], path))
            return [];
        // Rec Case
        path.Add((v, p));
        List<(NamedStrToken v, Str prefix)> ret = [];

        for (int j = 0; j < path.Count; j++) {
            Str r = [];
            r.AddRange(path[j].prefix, false);
            for (int k = j; k > 0; k--) {
                r.AddRange(path[k - 1].prefix, false);
            }
            for (int k = path.Count; k > j + 1; k--) {
                r.AddRange(path[k - 1].prefix, false);
            }
            ret.Add((path[j].v, r));
        }
        return ret;
    }

    static int splitEqCnt;

    ModifierBase? SplitEq(bool dir, Dictionary<NonTermInt, RatPoly> intSubst) {
        if (LHS.IsEmpty() || RHS.IsEmpty())
            return null;
        splitEqCnt++;
        BigRat constDiff = BigRat.Zero;

        // If we already know that there is some variable to afterwards
        BigInt? best = null;
        int bestLhs = -1, bestRhs = -1;

        // potentially better candidates, but we do not know yet that there is a variable coming
        BigInt? bestPending = null;
        int bestLhsPending = -1, bestRhsPending = -1;

        int lhsIdx = 1, rhsIdx = 1;

        IntPoly len = LenVar.MkLenPoly([LHS.Peek(dir, 0)]);
        RatPoly lhs = len.Apply(intSubst);
        constDiff += lhs.ConstPart;
        lhs.ElimConst();
        len = LenVar.MkLenPoly([RHS.Peek(dir, 0)]);
        RatPoly rhs = len.Apply(intSubst);
        constDiff -= rhs.ConstPart;
        rhs.ElimConst();

        // We ignore equal cases until we find the first variable
        bool seenVariable = false;

        while (lhsIdx < LHS.Count || rhsIdx < RHS.Count) {
            if (seenVariable && lhs.IsZero && rhs.IsZero && constDiff.IsInt) {
                if ((!bestPending.HasValue || BigInteger.Abs(constDiff.GetInt()) < bestPending)) {
                    bestPending = BigInteger.Abs(constDiff.GetInt());
                    bestLhsPending = lhsIdx;
                    bestRhsPending = rhsIdx;
                }
            }
            RatPoly? ratLen;
            StrToken t;
            if (lhs.IsEmpty() && rhs.IsNonEmpty() ||
                (lhs.IsEmpty() && rhs.IsEmpty() && constDiff.IsNeg)) {

                if (LHS.Count <= lhsIdx)
                    break;
                t = LHS.Peek(dir, lhsIdx++);
                if (t is NamedStrToken) {
                    if (bestPending.HasValue && (!best.HasValue || bestPending > best)) {
                        best = bestPending;
                        bestLhs = bestLhsPending;
                        bestRhs = bestRhsPending;
                        bestPending = null;
                        bestLhsPending = -1;
                        bestRhsPending = -1;
                    }
                    seenVariable = true;
                }
                len = LenVar.MkLenPoly([t]);
                ratLen = len.Apply(intSubst);
                constDiff += ratLen.ConstPart;
                ratLen.ElimConst();
                if (!ratLen.IsZero) {
                    lhs.Plus(ratLen);
                    RatPoly.ElimCommon(lhs, rhs);
                }
                continue;
            }
            if (RHS.Count <= rhsIdx)
                break;
            t = RHS.Peek(dir, rhsIdx++);
            if (t is NamedStrToken) {
                if (bestPending.HasValue && (!best.HasValue || bestPending > best)) {
                    best = bestPending;
                    bestLhs = bestLhsPending;
                    bestRhs = bestRhsPending;
                    bestPending = null;
                    bestLhsPending = -1;
                    bestRhsPending = -1;
                }
                seenVariable = true;
            }
            len = LenVar.MkLenPoly([t]);
            ratLen = len.Apply(intSubst);
            constDiff -= ratLen.ConstPart;
            ratLen.ElimConst();
            if (!ratLen.IsZero) {
                rhs.Plus(ratLen);
                RatPoly.ElimCommon(lhs, rhs);
            }
        }
        if (!best.HasValue)
            return null;
        Debug.Assert(bestLhs > 0);
        Debug.Assert(bestRhs > 0);
        // if the difference is > int.MaxValue we have other problems anyway...
        return !best.Value.TryGetInt(out int val) 
            ? null 
            : new EqSplitModifier(this, bestLhs, bestRhs, val, dir);
    }

    static int Periodicity(Str s, int from, int to) {
        if (from == to)
            // units are always a-periodic
            return to - from + 1;
        // Compute Knuth-Morris-Pratt prefix function
        Debug.Assert(from < to);

        int m = to - from + 1;
        int[] prefix = new int[m];
        prefix[0] = 0;
        int k = 0;

        for (int q = 1; q < m; q++) {
            while (k > 0 && !s.Peek(true, from + k).Equals(s.Peek(true, from + q))) {
                k = prefix[k - 1];
            }
            if (s.Peek(true, from + k).Equals(s.Peek(true, from + q)))
                k++;
            prefix[q] = k;
        }
        // if returning 0, we are acyclic
        return (to - from + 1) - prefix[^1];
    }

    static void GetParikhCandidates(Str s, int from, int to, HashSet<Str> pattern) {
        // TODO: Check if the pattern is already in the set (trie!)
        Debug.Assert(from < to);
        int p = Periodicity(s, from, to - 1);
        if (p == to - from) {
            pattern.Add(s.SubStr(from, to - from));
            return;
        }
        int rotLen = to - p - from;
        // All rotations of the base of the periodic base
        for (int i = from; i < to - rotLen; i++) {
            GetParikhCandidates(s, i, i + rotLen, pattern);
        }
    }

    static int GetNextChar(int from, Str s) {
        for (int i = from; i < s.Count; i++) {
            if (s[i] is CharToken)
                return i;
        }
        return s.Count;
    }

    static int GetNextNonChar(int from, Str s) {
        for (int i = from; i < s.Count; i++) {
            if (s[i] is not CharToken)
                return i;
        }
        return s.Count;
    }

    static HashSet<Str> GetParikhCandidates(Str s) {
        HashSet<Str> pattern = [];

        // [from; to)
        List<(int from, int to)> charIntervals = [];

        int from = GetNextChar(0, s);
        int to = from + 1;
        while (to < s.Count) {
            StrToken t = s.Peek(true, to);
            if (t is CharToken) {
                to++;
                continue;
            }
            if (to - from > 1)
                charIntervals.Add((from, to));
            from = GetNextChar(to + 1, s);
            to = from + 1;
        }

        if (from + 1 < s.Count)
            charIntervals.Add((from, s.Count));

        // TODO: We might not only find maximum ones, but it does not matter
        charIntervals.Sort((a, b) => - ((a.to - a.from) - (b.to - b.from)));

        for (int i = 0; i < charIntervals.Count; i++) {
            (from, to) = charIntervals[i];
            GetParikhCandidates(s, from, to, pattern);
        }
        return pattern;
    }

    static void GroupParik(Str s, Str pattern, Dictionary<Str, int> patternOcc, ref int constant, int sig) {
        Debug.Assert(pattern.Word);
        Debug.Assert(pattern.Count > 1);

        Str? runningStr = null;
        int i = 0;

        while (i < s.Count) {
            // find the start of the gap
            int k;
            int j;
            while (i < s.Count) {
                j = 0;
                for (; i + j < s.Count && j < pattern.Count; j++) {
                    if (!s[i + j].Equals(pattern[j]))
                        break;
                }
                if (j >= pattern.Count) {
                    // we found a proper occurrence
                    constant += sig;
                    i += j;
                    continue;
                }
                if (i + j >= s.Count) {
                    // end of string (we can directly break)
                    i = s.Count;
                    break;
                }
                if (s[i + j] is CharToken) {
                    // they just don't match
                    i++;
                    continue;
                }
                // we hit a gap
                runningStr = s.SubStr(i, j + 1);
                i += j + 1;
                break;
            }
            if (runningStr is null)
                break;

            // extend the gap (center case)
            while (i < s.Count) {
                if (s[i] is not CharToken) {
                    // consecutive non-variables; just add
                    runningStr.AddLast(s[i]);
                    i++;
                    continue;
                }
                j = GetNextNonChar(i, s);
                if (j - i >= pattern.Count || j >= s.Count)
                    break;
                // Check if it is in the center
                k = 1;
                for (; k < j - i; k++) {
                    int l = 0;
                    for (; l <= k; l++) {
                        if (!s[i + l].Equals(pattern[l + k]))
                            break;
                    }
                    if (l > k)
                        break;
                }
                if (k < j - i) {
                    // we have a center gap
                    runningStr.AddLastRange(s.SubStr(i, j - i + 1));
                    i = j + 1;
                    continue;
                }
                break;
            }
            // check for right gap
            j = Math.Min(GetNextNonChar(i, s) - i, Math.Min(pattern.Count, s.Count - i));
            // find the end of the gap (we look for the largest such k)
            for (; j > 1; j--) {
                int l = 1;
                for (; l < j; l++) {
                    if (!s[i + j - l - 1].Equals(pattern[^l]))
                        break;
                }
                if (l >= j)
                    break;
            }
            int tail = Math.Max(0, j - 1);
            runningStr.AddLastRange(s.SubStr(i, tail));
            i += tail;
            if (!patternOcc.TryGetValue(runningStr, out int v))
                patternOcc.Add(runningStr, sig);
            else
                patternOcc[runningStr] = v + sig;

            runningStr = null;
        }
        Debug.Assert(i >= s.Count);
    }

    static int OverApprox(Str gap) {
        Debug.Assert(gap.IsNonEmpty());
        Debug.Assert(gap.Any(o => o is not CharToken));
        if (gap.Count == 1)
            return 0;
        int overApprox = 0;
        if (gap[0] is CharToken)
            overApprox++;
        if (gap[^1] is CharToken)
            overApprox++;
        return gap.Count(o => o is not CharToken) + overApprox - 1;

    }

    static bool CheckMultiSequenceParikh(Str s1, Str s2, Str pattern) {
        Dictionary<Str, int> patternOcc = [];
        int constant = 0;
        GroupParik(s1, pattern, patternOcc, ref constant, 1);
        GroupParik(s2, pattern, patternOcc, ref constant, -1);

        int sum1 = constant;
        int sum2 = -constant;

        foreach (var gap in patternOcc) {
            if (gap.Value == 0)
                continue;
            int overapp = Math.Abs(gap.Value) * OverApprox(gap.Key);
            if (gap.Value < 0)
                sum1 += overapp;
            else
                sum2 += overapp;
        }
        return sum1 >= 0 && sum2 >= 0;
    }

    public static bool CheckMultiSequenceParikh(Str s1, Str s2) {
        var c = GetParikhCandidates(s1);
        var c2 = GetParikhCandidates(s2);
        c.UnionWith(c2);
        foreach (var s in c2) {
            Debug.Assert(s.Count > 0);
            if (s.Count < 2)
                continue;
            if (!CheckMultiSequenceParikh(s1, s2, s))
                return false;
        }
        return true;
    }

    ModifierBase? SplitSCharSChar(Str s1, Str s2, bool dir) {
        if (s1.IsEmpty() || s2.IsEmpty() || s1.Peek(dir) is not SymCharToken o1 || s2.Peek(dir) is not SymCharToken o2)
            return null;
        // Why could that happen?!
        Debug.Assert(false);
        return new SCharCharModifier(o1, o2);
    }

    ModifierBase? SplitVarVar(Str s1, Str s2, bool dir) {
        if (s1.IsEmpty() || s2.IsEmpty() || s1.Peek(dir) is not StrVarToken v1 || s2.Peek(dir) is not StrVarToken v2)
            return null;

        // Str? p1 = TryGetPowerSplitBase(v1, s2, dir);
        // Str? p2 = TryGetPowerSplitBase(v2, s1, dir);
        // if (p1 is not null && p2 is not null) {
        //     Debug.Assert(!p1.Ground || !p2.Ground); 
        //     if (p1.Ground) {
        //         Debug.Assert(false);
        //         return new CombinedModifier(
        //             new GPowerIntrModifier(v1, p1, dir),
        //             new ConstNielsenModifier(v2, v1, dir)
        //         );
        //         //return new GPowerPowerIntrModifier(v1, v2, p1, p2, dir);
        //     }
        //     if (p2.Ground) {
        //         Debug.Assert(false);
        //         return new CombinedModifier(
        //             new GPowerIntrModifier(v2, p2, dir),
        //             new ConstNielsenModifier(v1, v2, dir)
        //         );
        //     }
        //     // return new GPowerPowerIntrModifier(v2, v1, p2, p1, dir);
        //     return
        //         new VarNielsenModifier(v1, v2, dir);
        //     //return new PowerPowerIntrModifier(v1, v2, p1, p2, dir);
        // }
        // if (p1 is not null) {
        //     (p1, p2) = (p2, p1);
        //     (v1, v2) = (v2, v1);
        //     (s1, s2) = (s2, s1);
        // }
        // if (p1 is null)
        return new VarNielsenModifier(v1, v2, dir);
        //Debug.Assert(false);
        //if (p1.Ground)
        //    return new GPowerIntrConstNielsen(v1, v2, p1, dir);
        //return new PowerIntrConstNielsen(v1, v2, p1, dir);
    }

    ModifierBase? SplitGroundPower(StrToken t, Str s, Dictionary<NamedStrToken, Dictionary<NamedStrToken, Str>> varDep, bool dir) {
        if (t is not StrVarToken v || s.IsEmpty() || s.Peek(dir) is not UnitToken)
            return null;
        var p = TryGetPowerSplitBase(v, s, varDep, dir);
        return p.IsEmpty() ? null : new GPowerIntrModifier(p, dir);
    }

    ModifierBase? SplitVarChar(StrToken t, Str s, bool dir) {
        if (t is not StrVarToken v || s.IsEmpty() || s.Peek(dir) is not UnitToken)
            return null;
        // Str? p = TryGetPowerSplitBase(v, s, dir);
        // if (p is null)
        //     return new ConstNielsenModifier(v, s.Peek(dir), dir);
        // if (p.Ground) {
        //     Debug.Assert(false); // This should be excluded before (SplitGroundPower)
        //     return new GPowerIntrModifier(v, p, dir);
        // }
        return new ConstNielsenModifier(v, s.Peek(dir), dir);
        //return new PowerIntrModifier(v, p, dir);
    }

    ModifierBase? SplitVarPower(StrToken t, Str s, bool dir) {
        if (t is not StrVarToken v || s.IsEmpty() || s.Peek(dir) is not PowerToken { Ground: true } p)
            return null;

        // Str? b = TryGetPowerSplitBase(v, s, dir);
        // if (b is null)
        //     return new PowerSplitModifier(v, p, dir);
        // if (b.Ground)
        //     return new GPowerIntrModifier(v, b, dir);
        return new PowerSplitModifier(v, p, dir);
    }

    ModifierBase ExtendDir(Dictionary<NamedStrToken, Dictionary<NamedStrToken, Str>> varDep, Dictionary<NonTermInt, RatPoly> intSubst, bool dir) {
        Str s1 = LHS;
        Str s2 = RHS;
        SortStr(ref s1, ref s2, dir);
        if (s1.IsEmpty()) {
            Debug.Assert(!s2.IsEmpty());
            foreach (var s in s2) {
                if (s is PowerToken p)
                    return new PowerEpsilonModifier(p);
                // Simplify step should have already dealt with everything else!
                throw new NotSupportedException();
            }
            throw new NotSupportedException();
        }
        Debug.Assert(!s1.IsEmpty() && !s2.IsEmpty());

        var t1 = s1.Peek(dir);
        var t2 = s2.Peek(dir);

        ModifierBase? ret;

        if ((ret = SplitPowerElim(t1, s2, dir)) is not null)
            return ret;
        if ((ret = SplitPowerElim(t2, s1, dir)) is not null)
            return ret;
        if (t2 is not NamedStrToken && (ret = SplitPowerUnwind(t1, false)) is not null)
            return ret;
        if (t1 is not NamedStrToken && (ret = SplitPowerUnwind(t2, false)) is not null)
            return ret;
        if ((ret = SplitGroundPower(t1, s2, varDep, dir)) is not null)
            return ret;
        if ((ret = SplitGroundPower(t2, s1, varDep, dir)) is not null)
            return ret;
        if ((ret = SplitEq(dir, intSubst)) is not null)
            return ret;
        if ((ret = SplitVarPower(t1, s2, dir)) is not null)
            return ret;
        if ((ret = SplitVarPower(t2, s1, dir)) is not null)
            return ret;
        if ((ret = SplitVarChar(t1, s2, dir)) is not null)
            return ret;
        if ((ret = SplitVarChar(t2, s1, dir)) is not null)
            return ret;
        if ((ret = SplitSCharSChar(s1, s2, dir)) is not null)
            return ret;
        if ((ret = SplitVarVar(s1, s2, dir)) is not null)
            return ret;
        if ((ret = SplitPowerUnwind(t1, true)) is not null)
            return ret;
        if ((ret = SplitPowerUnwind(t2, true)) is not null)
            return ret;
        throw new NotSupportedException();
    }

    static int extendCnt;

    public override ModifierBase Extend(NielsenNode node, Dictionary<NonTermInt, RatPoly> intSubst) {
        extendCnt++;
        // Don't sort -- this should have happened before in simplify!!
#if DEBUG
        Str lhs = LHS;
        Str rhs = RHS;
        SortStr(ref lhs, ref rhs, true);
        Debug.Assert(ReferenceEquals(lhs, LHS));
        Debug.Assert(ReferenceEquals(rhs, RHS));
#endif
        var m1 = ExtendDir(node.forwardVarDep, intSubst, true);
        var m2 = ExtendDir(node.backwardVarDep, intSubst, false);
#if DEBUG
        lhs = LHS;
        rhs = RHS;
        SortStr(ref lhs, ref rhs, true);
        Debug.Assert(ReferenceEquals(lhs, LHS));
        Debug.Assert(ReferenceEquals(rhs, RHS));
#endif
        return m1.CompareTo(m2) <= 0 ? m1 : m2;
    }

    public override int CompareToInternal(StrConstraint other) {
        StrEq otherEq = (StrEq)other;
        int cmp = LHS.Count.CompareTo(otherEq.LHS.Count);
        if (cmp != 0)
            return cmp;
        cmp = RHS.Count.CompareTo(otherEq.RHS.Count);
        if (cmp != 0)
            return cmp;
        cmp = LHS.CompareTo(otherEq.LHS);
        return cmp != 0 ? cmp : RHS.CompareTo(otherEq.RHS);
    }

    public override StrConstraint Negate() => 
        new StrNonEq(LHS, RHS, Dependencies.Clone());

    public override BoolExpr ToExpr(NielsenGraph graph) {
        return graph.Ctx.MkEq(LHS.ToExpr(graph), RHS.ToExpr(graph));
    }

    public override int GetHashCode() {
        return 613461011 + LHS.GetHashCode() + 967118167 * RHS.GetHashCode();
    }

    public override string ToString() => $"{LHS} = {RHS}";
}