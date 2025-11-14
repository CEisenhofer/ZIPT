using Microsoft.Z3;
using System.Diagnostics;
using System.Numerics;
using ZIPT.Constraints.ConstraintElement.AuxConstraints;
using ZIPT.Constraints.Modifier;
using ZIPT.IntUtils;
using ZIPT.MiscUtils;
using ZIPT.Strings.Chunks;
using ZIPT.Strings.Tokens;

namespace ZIPT.Constraints.ConstraintElement;

public sealed class StrEq : StrEqBase {

    public StrEq(Str lhs, Str rhs) : base(lhs, rhs) {
        Debug.Assert(lhs.RegexFree);
        Debug.Assert(rhs.RegexFree);
    }

    public override StrEq Apply(Subst subst, NielsenNode node) {
        var lhs = node.Env.StrManager.Subst(LHS, subst);
        var rhs = node.Env.StrManager.Subst(RHS, subst);
        SortStr(ref lhs, ref rhs, true);
        if (ReferenceEquals(lhs, LHS) && ReferenceEquals(rhs, RHS))
            return this;
        return new StrEq(lhs, rhs);
    }

    public override StrEq Apply(CharSubst subst, NielsenNode node) {
        var lhs = node.Env.StrManager.Subst(node.Env, LHS, subst);
        var rhs = node.Env.StrManager.Subst(node.Env, RHS, subst);
        SortStr(ref lhs, ref rhs, true);
        if (ReferenceEquals(lhs, LHS) && ReferenceEquals(rhs, RHS))
            return this;
        return new StrEq(lhs, rhs);
    }

    public override StrEq Apply(Interpretation itp) {
        var lhs = itp.Env.StrManager.Subst(LHS, itp);
        var rhs = itp.Env.StrManager.Subst(RHS, itp);
        SortStr(ref lhs, ref rhs, true);
        if (ReferenceEquals(lhs, LHS) && ReferenceEquals(rhs, RHS))
            return this;
        return new StrEq(lhs, rhs);
    }


    public void GetNielsenDep(Environment env, Dictionary<NamedStrToken, Dictionary<NamedStrToken, List<StrToken>>> varDep, bool fwd) {
        if (LHS.IsEmpty() || RHS.IsEmpty())
            return;
        // TODO: Optimize this
        Str s1 = LHS;
        Str s2 = RHS;
        var t1 = s1[fwd];
        var t2 = s2[fwd];
        if (t2 is NamedStrToken) {
            (s1, s2) = (s2, s1);
            (t1, t2) = (t2, t1);
        }
        if (t1 is not NamedStrToken v1)
            return;
        if (t2 is NamedStrToken v2) {
            Debug.Assert(!v1.Equals(v2));
            if (!varDep.TryGetValue(v1, out var varSet))
                varDep.Add(v1, varSet = []);
            varSet[v2] = [];
            if (!varDep.TryGetValue(v2, out varSet))
                varDep.Add(v2, varSet = []);
            varSet[v1] = [];
            return;
        }
        List<StrToken> s = [];
        for (int i = 0; i < s2.Length; i++) {
            var t = s2[fwd, i];
            if (t is NamedStrToken v3) {
                if (!varDep.TryGetValue(v1, out var varSet))
                    varDep.Add(v1, varSet = []);
                if (varSet.TryGetValue(v3, out var old)) {
                    if (old.Count <= s.Count)
                        return;
                    varSet[v3] = old;
                    return;
                }
                varSet.Add(v3, s);
                return;
    }
            s.Add(t);
        }
    }

    static bool HasDepCycle(NamedStrToken x, NamedStrToken to, Dictionary<NamedStrToken, Dictionary<NamedStrToken, List<StrToken>>> varDep, HashSet<NamedStrToken> visited, List<(NamedStrToken v, List<StrToken> prefix)> path) {
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

    public void SimplifyUnitNielsen(Environment env, DetModifier sConstr,
        Dictionary<NamedStrToken, Dictionary<NamedStrToken, List<StrToken>>> varDep,
        Dictionary<NamedStrToken, Dictionary<NamedStrToken, uint>> largerVars,
        Dictionary<NamedStrToken, uint> lowerBounds, bool fwd) {

        SortStr();
        if (LHS.IsEmpty())
            return;

        Str s1 = LHS;
        Str s2 = RHS;
        StrToken t1 = s1[fwd];
        StrToken t2 = s2[fwd];

        if (t2 is NamedStrToken) {
            (s1, s2) = (s2, s1);
            (t1, t2) = (t2, t1);
        }
        // if there is a variable then there is one at position 1
        if (t1 is not NamedStrToken v1) 
            return;

        // check unit cases by lengths
        List<StrToken> s = [];
        int i;
        if (lowerBounds.TryGetValue(v1, out uint lowerBound) |
            largerVars.TryGetValue(v1, out var larger)) {

            for (i = 0; i < s2.Length; i++) {
                t2 = s2[fwd, i];
                if (lowerBound > 0 && t2 is UnitToken u2) {
                    lowerBound--;
                    s.Add(u2);
                    continue;
                }
                if (larger is not null && t2 is NamedStrToken v2 && larger.TryGetValue(v2, out uint val)) {
                    Debug.Assert(val > 0);
                    val--;
                    if (val == 0)
                        larger.Remove(v2);
                    else
                        larger[v2] = val;
                    s.Add(v2);
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
            sConstr.Add(new Subst(v1, env.MkString(s)));
            return;
        }

        if (t2 is not CharToken || s1.Length <= 1)
            return;

        // check unit cases by look-ahead
        Debug.Assert(s2.IsNonEmpty());

        // uyw = xvw' and u, v ground and x does not depend on y (otw. we would result in an infinite sequence of unit propagations if it is unsat)
        // x / u' x with u' <= u while u' incompatible with v and u' is char only
        i = 0;
        for (; i < s2.Length && s2[fwd, i] is CharToken; i++) {
            // TODO: Use consistent prefix (requires some resource improvements first though)
            int j1 = 1;
            int j2 = i;
            bool failed = false;
            while (j1 < s1.Length && j2 < s2.Length) {
                StrToken st1 = s1[fwd, j1];
                StrToken st2 = s2[fwd, j2];
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
                for (int l = 0; j2 < s2.Length && l < i; l++) {
                    st2 = s2[fwd, j2];
                    if (st2 is not CharToken) {
                        incomparable = true;
                        // We cannot say - abort
                        break;
                    }
                    Debug.Assert(s2[fwd, l] is CharToken);
                    if (st2.Equals(s2[fwd, l])) {
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
        for (; k < s2.Length; k++) {
            t = s2[fwd, k];
            if (t is NamedStrToken/* or PowerToken*/)
                break;
        }
        if (k < s2.Length) {
            t = s2[fwd, k];
            Debug.Assert(t is not null);
            if (/*t is PowerToken || */HasDepCycle((NamedStrToken)t, v1, varDep, [], []))
                // We also skip powers, as e.g., xy a^n a = yx b z would add infinitely many F / Fa because 
                // length constraint |y| + |x| + n + 1 = |x| + |y| + 1 + |z| would just make n bigger, making a^n unwinding once more
                return;
        }
        var tokens = new StrToken[i + 1];
        for (int j = 0; j < i; j++) {
            tokens[j] = s2[fwd, j];
        }
        tokens[i] = v1;
        sConstr.Add(new Subst(v1, env.MkString(tokens, fwd)));
    }

    // Try to add the substitution: x / s ==> do an occurrence check. If it fails, we have to add it as an ordinary equation
    public bool AddDefinition(StrVarToken v, Str s, NielsenNode node, DetModifier sConstr) {
        if (s.ContainsVar(v))
            return false;
        sConstr.Add(new Subst(v, s));
        return true;
    }

    SimplifyResult SimplifyDir(LocalInfo info, DetModifier sConstr, bool fwd) {
        while (LHS.IsNonEmpty() && RHS.IsNonEmpty()) {
            SortStr(fwd);
            Debug.Assert(LHS.Length > 0);
            Debug.Assert(RHS.Length > 0);
            Debug.Assert(LHS.RegexFree);
            Debug.Assert(RHS.RegexFree);

            if (SimplifySame(info.Env, fwd))
                continue;

            var t1 = LHS[fwd];
            var t2 = RHS[fwd];

            if (t1 is CharToken c1 && t2 is CharToken c2 && !c1.Equals(c2))
                return SimplifyResult.Conflict;

            if (t1 is SymCharToken sc1 && t2 is UnitToken u) {
                sConstr.Add(new CharSubst(sc1, u));
                return SimplifyResult.Restart;
            }

            if (t1 is PowerToken p1) {
                if (info.CurrentNode.IsZero(p1.Power)) {
                    LHS = info.Env.StrManager.Drop(LHS, fwd);
                    continue;
                }
                if (!IsPrefixConsistent(info.CurrentNode, p1.Base, RHS, fwd)) {
                    sConstr.Add(new IntEq(info.Env.ZeroInt, p1.Power));
                    return SimplifyResult.Proceed;
                }
            }
            if (t2 is PowerToken p2) {
                if (info.CurrentNode.IsZero(p2.Power)) {
                    RHS = info.Env.StrManager.Drop(RHS, fwd);
                    continue;
                }
                if (!IsPrefixConsistent(info.CurrentNode, p2.Base, LHS, fwd)) {
                    sConstr.Add(new IntEq(info.Env.ZeroInt, p2.Power));
                    return SimplifyResult.Proceed;
                }
            }

            if (SimplifyPower(info, fwd))
                continue;
            break;
        }
        return SimplifyResult.Proceed;
    }

    static int simplifyCount;

    protected override SimplifyResult SimplifyAndPropagateInternal(LocalInfo info, DetModifier sConstr,
        ref BacktrackReasons reason) {
        simplifyCount++;
        Log.WriteLine($"Simplify Eq ({simplifyCount}): {LHS} = {RHS}");
#if false
        lhs = LcpCompression(lhs) ?? lhs;
        rhs = LcpCompression(rhs) ?? rhs;
#endif
        if (SimplifyDir(info, sConstr, true) == SimplifyResult.Conflict) {
            reason = BacktrackReasons.SymbolClash;
            return SimplifyResult.Conflict;
        }

        if (SimplifyDir(info, sConstr, false) == SimplifyResult.Conflict) {
            reason = BacktrackReasons.SymbolClash;
            return SimplifyResult.Conflict;
        }

        if (LHS.IsEmpty() && RHS.IsEmpty())
            return SimplifyResult.Satisfied;

        if (LHS.IsEmpty() || RHS.IsEmpty()) {
            var eq = LHS.IsEmpty() ? RHS : LHS;
            // Remove powers that actually do not exist anymore
            while (eq.IsNonEmpty() && eq[true] is PowerToken p) {
                Str? s;
                if ((s = SimplifyPowerSingle(info, p)) is not null) {
                    eq = info.Env.StrManager.DropLeft(eq);
                    eq = info.Env.StrManager.Concat(eq, s);
                    continue;
                }
                break;
            }
            if (eq.IsEmpty())
                return SimplifyResult.Satisfied;
            if (SimplifyEmpty(eq.GetEnumerator(), info.CurrentNode, sConstr) == SimplifyResult.Conflict) {
                reason = BacktrackReasons.SymbolClash;
                return SimplifyResult.Conflict;
            }
            LHS = eq;
            RHS = info.Env.EmptyStr;
            SortStr();
            return SimplifyResult.Proceed;
        }

#if false
        // Check Multiset abstraction
        var lhsSet = LHS.ToSet();
        var rhsSet = RHS.ToSet();
        MSet<StrToken, BigInteger>.ElimCommon(lhsSet, rhsSet);
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
        if (lhsSet.IsNonEmpty() && rhsSet.IsNonEmpty()) {
            if (lhsSet.All(o => o.t is CharToken) &&
                rhsSet.All(o => o.t is CharToken)) {
                reason = BacktrackReasons.ParikhImage;
                return SimplifyResult.Conflict;
            }
            /*if (CheckMultiSequenceParikh(LHS, RHS)) {
                reason = BacktrackReasons.ParikhImage;
                return SimplifyResult.Conflict;
            }*/
        }
#endif

        // Propagate assignments
        // important: clone it; otherwise one might into endless recursions when applied to itself
        if (LHS is { Length: 1, First: StrVarToken s1 }) {
            if (AddDefinition(s1, RHS, info.CurrentNode, sConstr))
                return SimplifyResult.RestartAndSatisfied;
        }
        else if (RHS is { Length: 1, First: StrVarToken s2 }) {
            if (AddDefinition(s2, LHS, info.CurrentNode, sConstr))
                return SimplifyResult.RestartAndSatisfied;
        }
        SortStr();
        return SimplifyResult.Proceed;
    }

    static NumCmpModifier? SplitPowerElim(StrToken t, Str s, Environment env, bool fwd) {
        if (t is not PowerToken p1)
            return null;
        var r = CommPower(p1.Base, s, env, fwd);
        return r.idx > 0 ? new NumCmpModifier(p1.Power, r.num) : null;
    }

    static NumUnwindingModifier? SplitPowerUnwind(StrToken t, bool varInvolved) => 
        t is not PowerToken p ? null : (varInvolved ? new VarNumUnwindingModifier(p.Power) : new ConstNumUnwindingModifier(p.Power));

    static List<(NamedStrToken x, Str val)> TryGetPowerSplitBase(StrVarToken v, Str s, Environment env, Dictionary<NamedStrToken, Dictionary<NamedStrToken, List<StrToken>>> varDep, bool fwd) {
        if (s.IsEmpty())
            return [];
        List<StrToken> p = [];
        var i = 0;
        for (; i < s.Length && s[fwd, i] is not NamedStrToken; i++) {
            p.Add(s[fwd, i]);
        }

        if (i >= s.Length)
            // Non-rec Case
            return [];

        var x = (NamedStrToken)s[fwd, i];
        List<(NamedStrToken v, List<StrToken> prefix)> path = [];

        if (!HasDepCycle(x, v, varDep, [], path))
            return [];
        // Rec Case
        path.Add((v, p));
        List<(NamedStrToken v, Str prefix)> ret = [];

        for (int j = 0; j < path.Count; j++) {
            List<StrToken> r = [];
            r.AddRange(path[j].prefix);
            for (int k = j; k > 0; k--) {
                r.AddRange(path[k - 1].prefix);
            }
            for (int k = path.Count; k > j + 1; k--) {
                r.AddRange(path[k - 1].prefix);
            }
            ret.Add((path[j].v, env.MkString(r, fwd)));
        }
        return ret;
    }

    static int splitEqCnt;

    ModifierBase? SplitEq(bool fwd, Environment env/*, Dictionary<NamedInt, PDD<BigRational>> intSubst*/) {
        if (LHS.IsEmpty() || RHS.IsEmpty())
            return null;
        if (!LHS.RegexFree || !RHS.RegexFree)
            // Actually we would need to stop only once we hit a regex token
            return null;
        splitEqCnt++;
        BigInteger constDiff = BigInteger.Zero;

        BigInteger? best = null;
        int bestLhs = -1, bestRhs = -1;

        // potentially better candidates, but we do not know yet that there is a variable coming
        BigInteger? bestPending = null;
        int bestLhsPending = -1, bestRhsPending = -1;

        int lhsIdx = 1, rhsIdx = 1;

        //PDD<BigInteger> len = LenVar.MkLenPoly([LHS[dir]], env);
        //PDD<BigRational> lhsLen = len.Apply(intSubst);
        var lhsLen = LenVar.MkLenPoly([LHS[fwd]], env, []);
        constDiff += lhsLen.ConstOffset;

        //len = LenVar.MkLenPoly([RHS[dir]], env);
        //PDD<BigRational> rhsLen = len.Apply(intSubst);
        var rhsLen = LenVar.MkLenPoly([RHS[fwd]], env, []);
        constDiff -= rhsLen.ConstOffset;

        // We ignore equal cases until we find the first variable
        bool seenVariable = false;

        while (lhsIdx < LHS.Length || rhsIdx < RHS.Length) {
            if (seenVariable && lhsLen.IsZero && rhsLen.IsZero) {
                if ((!bestPending.HasValue || BigInteger.Abs(constDiff) < bestPending)) {
                    bestPending = BigInteger.Abs(constDiff);
                    bestLhsPending = lhsIdx;
                    bestRhsPending = rhsIdx;
                }
            }
            StrToken t;
            PDD<BigInteger>? len;
            if (lhsLen.IsZero && !rhsLen.IsZero ||
                (lhsLen.IsZero && rhsLen.IsZero && constDiff.Sign < 0)) {

                if (LHS.Length <= lhsIdx)
                    break;
                t = LHS[fwd, lhsIdx++];
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
                len = LenVar.MkLenPoly([t], env, []);
                //ratLen = len.Apply(intSubst);
                constDiff += len.ConstOffset;
                lhsLen = lhsLen.Add(len);
                continue;
            }
            if (RHS.Length <= rhsIdx)
                break;
            t = RHS[fwd, rhsIdx++];
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
            len = LenVar.MkLenPoly([t], env, []);
            //ratLen = len.Apply(intSubst);
            constDiff -= len.ConstOffset;
            rhsLen = rhsLen.Add(len);
        }
        if (!best.HasValue)
            return null;
        Debug.Assert(bestLhs > 0);
        Debug.Assert(bestRhs > 0);
        // if the difference is > int.MaxValue we have other problems anyway...
        return
            best > int.MaxValue ||
            best < int.MinValue
                ? null
                : new EqSplitModifier(this, (uint)bestLhs, (uint)bestRhs, (int)best, fwd);
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
            while (k > 0 && !s[true, from + k].Equals(s[true, from + q])) {
                k = prefix[k - 1];
            }
            if (s[true, from + k].Equals(s[true, from + q]))
                k++;
            prefix[q] = k;
        }
        // if returning 0, we are acyclic
        return (to - from + 1) - prefix[^1];
    }

    static void GetParikhCandidates(Environment env, Str s, int from, int to, HashSet<Str> pattern) {
        // TODO: Check if the pattern is already in the set (trie!)
        Debug.Assert(from < to);
        int p = Periodicity(s, from, to - 1);
        if (p == to - from) {
            pattern.Add(env.StrManager.SubStr(s, from, to - from));
            return;
        }
        int rotLen = to - p - from;
        // All rotations of the base of the periodic base
        for (int i = from; i < to - rotLen; i++) {
            GetParikhCandidates(env, s, i, i + rotLen, pattern);
        }
    }

    static int GetNextChar(int from, Str s) {
        for (int i = from; i < s.Length; i++) {
            if (s[i] is CharToken)
                return i;
        }
        return (int)s.Length;
    }

    static int GetNextNonChar(int from, Str s) {
        for (int i = from; i < s.Length; i++) {
            if (s[i] is not CharToken)
                return i;
        }
        return (int)s.Length;
    }

    static HashSet<Str> GetParikhCandidates(Environment env, Str s) {
        // [from; to)
        List<(int from, int to)> charIntervals = [];

        int from = GetNextChar(0, s);
        int to = from + 1;
        while (to < s.Length) {
            StrToken t = s[true, to];
            if (t is CharToken) {
                to++;
                continue;
            }
            if (to - from > 1)
                charIntervals.Add((from, to));
            from = GetNextChar(to + 1, s);
            to = from + 1;
        }

        if (from + 1 < s.Length)
            charIntervals.Add((from, (int)s.Length));

        // TODO: We might not only find maximum ones, but it does not matter
        charIntervals.Sort((a, b) => - ((a.to - a.from) - (b.to - b.from)));
        HashSet<Str> pattern = [];

        for (int i = 0; i < charIntervals.Count; i++) {
            (from, to) = charIntervals[i];
            GetParikhCandidates(env, s, from, to, pattern);
        }
        return pattern;
    }

    static void GroupParikh(Environment env, Str s, Str pattern, IDictionary<Str, int> patternOcc, ref int constant, int sign) {
        Debug.Assert(pattern.GetEnumerator().All(o => o is CharToken));
        Debug.Assert(pattern.Length > 1);

        List<StrToken>? runningStr = null;
        int i = 0;

        while (i < s.Length) {
            // find the start of the gap
            int k;
            int j;
            while (i < s.Length) {
                j = 0;
                for (; i + j < s.Length && j < pattern.Length; j++) {
                    if (!s[i + j].Equals(pattern[j]))
                        break;
                }
                if (j >= pattern.Length) {
                    // we found a proper occurrence
                    constant += sign;
                    i += j;
                    continue;
                }
                if (i + j >= s.Length) {
                    // end of string (we can directly break)
                    i = (int)s.Length;
                    break;
                }
                if (s[i + j] is CharToken) {
                    // they just don't match
                    i++;
                    continue;
                }
                // we hit a gap
                runningStr = env.StrManager.SubStr(s, i, j + 1).ToArray().ToList();
                i += j + 1;
                break;
            }
            if (runningStr is null)
                break;

            // extend the gap (center case)
            while (i < s.Length) {
                if (s[i] is not CharToken) {
                    // consecutive non-variables; just add
                    runningStr.Add(s[i]);
                    i++;
                    continue;
                }
                j = GetNextNonChar(i, s);
                if (j - i >= pattern.Length || j >= s.Length)
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
                    runningStr.AddRange(env.StrManager.SubStr(s, i, j - i + 1).ToArray());
                    i = j + 1;
                    continue;
                }
                break;
            }
            // check for right gap
            j = Math.Min(GetNextNonChar(i, s) - i, Math.Min((int)pattern.Length, (int)s.Length - i));
            // find the end of the gap (we look for the largest such k)
            for (; j > 1; j--) {
                int l = 1;
                for (; l < j; l++) {
                    if (!s[i + j - l - 1].Equals(pattern[false, l - 1]))
                        break;
                }
                if (l >= j)
                    break;
            }
            int tail = Math.Max(0, j - 1);
            runningStr.AddRange(env.StrManager.SubStr(s, i, tail).ToArray());
            i += tail;
            Str r = env.MkString(runningStr);
            if (!patternOcc.TryGetValue(r, out int v))
                patternOcc.Add(r, sign);
            else
                patternOcc[r] = v + sign;

            runningStr = null;
        }
        Debug.Assert(i >= s.Length);
    }

    static int OverApprox(Str gap) {
        Debug.Assert(gap.IsNonEmpty());
        Debug.Assert(gap.GetEnumerator().Any(o => o is not CharToken));
        if (gap.Length == 1)
            return 0;
        int overApprox = 0;
        if (gap.First is CharToken)
            overApprox++;
        if (gap.Last is CharToken)
            overApprox++;
        return gap.GetEnumerator().Count(o => o is not CharToken) + overApprox - 1;

    }

    static bool CheckMultiSequenceParikh(Environment env, Str s1, Str s2, Str pattern) {
        Dictionary<Str, int> patternOcc = [];
        int constant = 0;
        GroupParikh(env, s1, pattern, patternOcc, ref constant, 1);
        GroupParikh(env, s2, pattern, patternOcc, ref constant, -1);

        int sum1 = constant;
        int sum2 = -constant;

        foreach (var gap in patternOcc) {
            if (gap.Value == 0)
                continue;
            int overApprox = Math.Abs(gap.Value) * OverApprox(gap.Key);
            if (gap.Value < 0)
                sum1 += overApprox;
            else
                sum2 += overApprox;
        }
        return sum1 >= 0 && sum2 >= 0;
    }

    public static bool CheckMultiSequenceParikh(Environment env, Str s1, Str s2) {
        var c = GetParikhCandidates(env, s1);
        var c2 = GetParikhCandidates(env, s2);
        c.UnionWith(c2);
        foreach (var s in c2) {
            Debug.Assert(s.IsNonEmpty());
            if (s.Length < 2)
                continue;
            if (!CheckMultiSequenceParikh(env, s1, s2, s))
                return false;
        }
        return true;
    }

    static ModifierBase? SplitVarVar(Str s1, Str s2, bool fwd) {
        if (s1.IsEmpty() || s2.IsEmpty() || s1[fwd] is not StrVarToken v1 || s2[fwd] is not StrVarToken v2)
            return null;
        return new VarNielsenModifier(v1, v2, fwd);
    }

    ModifierBase? SplitGroundPower(StrToken t, Str s, Environment env, Dictionary<NamedStrToken, Dictionary<NamedStrToken, List<StrToken>>> varDep, bool fwd) {
        if (t is not StrVarToken v || s.IsEmpty() || s[fwd] is NamedStrToken)
            return null;
        var p = TryGetPowerSplitBase(v, s, env, varDep, fwd);
        return p.Count == 0 ? null : new GPowerIntrModifier(p, fwd);
    }

    ModifierBase? SplitVarChar(StrToken t, Str s, bool fwd) {
        if (t is not StrVarToken v || s.IsEmpty() || s[fwd] is not UnitToken)
            return null;
        return new ConstNielsenModifier(v, s[fwd], fwd);
    }

    ModifierBase? SplitVarPower(StrToken t, Str s, bool fwd) {
        if (t is not StrVarToken v || s.IsEmpty() || s[fwd] is not PowerToken { Ground: true } p)
            return null;
        return new PowerSplitModifier(v, p, fwd);
    }

    ModifierBase ExtendDir(Dictionary<NamedStrToken, Dictionary<NamedStrToken, List<StrToken>>> varDep, Environment env, Dictionary<NamedInt, PDD<BigRational>> intSubst, bool fwd) {
        Debug.Assert(IsSorted());
        if (LHS.IsEmpty()) {
            Debug.Assert(!RHS.IsEmpty());
            var t = RHS[true];
            if (t is PowerToken p)
                return new PowerEpsilonModifier(p);
            // Simplify step should have already dealt with everything else!
            throw new NotSupportedException();
        }
        Debug.Assert(!LHS.IsEmpty() && !RHS.IsEmpty());

        var t1 = LHS[fwd];
        var t2 = RHS[fwd];

        ModifierBase? ret;

        if ((ret = SplitPowerElim(t1, RHS, env, fwd)) is not null)
            return ret;
        if ((ret = SplitPowerElim(t2, LHS, env, fwd)) is not null)
            return ret;
        if (t2 is not NamedStrToken && (ret = SplitPowerUnwind(t1, false)) is not null)
            return ret;
        if (t1 is not NamedStrToken && (ret = SplitPowerUnwind(t2, false)) is not null)
            return ret;
        if ((ret = SplitGroundPower(t1, RHS, env, varDep, fwd)) is not null)
            return ret;
        if ((ret = SplitGroundPower(t2, LHS, env, varDep, fwd)) is not null)
            return ret;
        if ((ret = SplitEq(fwd, env/*, intSubst*/)) is not null)
            return ret;
        if ((ret = SplitVarPower(t1, RHS, fwd)) is not null)
            return ret;
        if ((ret = SplitVarPower(t2, LHS, fwd)) is not null)
            return ret;
        if ((ret = SplitVarChar(t1, RHS, fwd)) is not null)
            return ret;
        if ((ret = SplitVarChar(t2, LHS, fwd)) is not null)
            return ret;
        if ((ret = SplitVarVar(LHS, RHS, fwd)) is not null)
            return ret;
        if ((ret = SplitPowerUnwind(t1, true)) is not null)
            return ret;
        if ((ret = SplitPowerUnwind(t2, true)) is not null)
            return ret;
        throw new NotSupportedException();
    }

    static int extendCnt;

    public override ModifierBase? Extend(NielsenNode node, Dictionary<NamedInt, PDD<BigRational>> intSubst) {
        extendCnt++;
        // Don't sort -- this should have happened before in simplify!!
        var m1 = ExtendDir(node.forwardVarDep, node.Env, intSubst, true);
        var m2 = ExtendDir(node.backwardVarDep, node.Env, intSubst, false);
        return m1.CompareTo(m2) <= 0 ? m1 : m2;
    }

    public override int CompareToInternal(StrConstraint other) {
        StrEq otherEq = (StrEq)other;
        int cmp = LHS.Length.CompareTo(otherEq.LHS.Length);
        if (cmp != 0)
            return cmp;
        cmp = RHS.Length.CompareTo(otherEq.RHS.Length);
        if (cmp != 0)
            return cmp;
        cmp = LHS.CompareTo(otherEq.LHS);
        return cmp != 0 ? cmp : RHS.CompareTo(otherEq.RHS);
    }

    public override StrNonEq Negate() => new(LHS, RHS);

    public override BoolExpr ToExpr(Environment env, Dictionary<NamedStrToken, int> currentModificationCnt) => 
        env.Ctx.MkEq(LHS.ToExpr(env, currentModificationCnt), RHS.ToExpr(env, currentModificationCnt));

    public override int GetHashCode() => 
        HashCode.Combine(LHS.GetHashCode(), RHS.GetHashCode()) * 782620193;

    public override string ToString() => $"{LHS} = {RHS}";
}