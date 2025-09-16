using Microsoft.Z3;
using System.Diagnostics;
using System.Numerics;
using ZIPT.Constraints.ConstraintElement.AuxConstraints;
using ZIPT.Constraints.Modifier;
using ZIPT.IntUtils;
using ZIPT.MiscUtils;
using ZIPT.Strings;
using ZIPT.Strings.Chunks;
using ZIPT.Strings.Tokens;

namespace ZIPT.Constraints.ConstraintElement;

public sealed class StrEq : StrEqBase {

    public StrEq(Str lhs, Str rhs) : base(lhs, rhs) { }

    public override StrEq Apply(Subst subst, NielsenNode node) =>
        new(node.Env.StrManager.Subst(LHS, subst),
            node.Env.StrManager.Subst(RHS, subst));

    public override StrEq Apply(Interpretation itp) =>
        new(itp.Env.StrManager.Subst(LHS, itp),
            itp.Env.StrManager.Subst(RHS, itp));


    public void GetNielsenDep(Environment env, Dictionary<NamedStrToken, Dictionary<NamedStrToken, List<StrToken>>> varDep, bool dir) {
        if (LHS.IsEmpty() || RHS.IsEmpty())
            return;
        // TODO: Optimize this
        Str s1 = LHS;
        Str s2 = RHS;
        var t1 = s1[dir];
        var t2 = s2[dir];
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
            var t = s2[dir, i];
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

        if (s.IsNonEmpty()) 
            sConstr.Add(new Subst(v1, env.MkString(s)));

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

    static SimplifyResult SimplifyEmpty(IEnumerable<StrToken> s, NielsenNode node, DetModifier constr) {
        foreach (var t in s) {
            if (t is UnitToken)
                return SimplifyResult.Conflict;
            if (t is StrVarToken v)
                return constr.Add(new Subst(v, node.Env.EmptyStr));
            if (t is PowerToken p) {
                if (node.IsLt(node.Env.ZeroInt, p.Power))
                    // p.Power > 0
                    constr.Add(new StrEq(p.Base, node.Graph.Env.EmptyStr));
                else if (!StrManager.IsNullable(node, p.Base))
                    // p.Base != ""
                    constr.Add(new IntEq(p.Power));
            }
            else
                throw new NotSupportedException();
        }
        return SimplifyResult.Proceed;
    }

    // Try to add the substitution: x / s ==> do an occurrence check. If it fails, we have to add it as an ordinary equation
    public SimplifyResult AddDefinition(StrVarToken v, Str s, NielsenNode node, DetModifier sConstr) =>
        s.ContainsVar(v) 
            ? SimplifyResult.Proceed 
            : sConstr.Add(new Subst(v, s));

    SimplifyResult SimplifyDir(NielsenNode node, DetModifier sConstr, bool fwd) {
        // This can cause problems, as it might unwind/compress the beginning/end over and over again (might even detect it as subsumed)
        while (LHS.IsNonEmpty() && RHS.IsNonEmpty()) {
            SortStr(fwd);
            Debug.Assert(LHS.Length > 0);
            Debug.Assert(RHS.Length > 0);

            if (SimplifySame(node.Env, fwd))
                continue;

            var t1 = LHS[fwd];
            var t2 = RHS[fwd];

            if (t1 is CharToken c1 && t2 is CharToken c2 && !c1.Equals(c2))
                return SimplifyResult.Conflict;

            //if (t1 is SymCharToken sc1 && t2 is UnitToken u)
            //    return sConstr.Add(new SubstSChar(sc1, u));

            if (t1 is PowerToken p1) {
                if (node.IsZero(p1.Power)) {
                    LHS = node.Env.StrManager.Drop(LHS, fwd);
                    continue;
                }
                if (!IsPrefixConsistent(node, p1.Base, RHS, fwd)) {
                    sConstr.Add(new IntEq(node.Env.ZeroInt, p1.Power));
                    return SimplifyResult.Proceed;
                }
            }
            if (t2 is PowerToken p2) {
                if (node.IsZero(p2.Power)) {
                    RHS = node.Env.StrManager.Drop(RHS, fwd);
                    continue;
                }
                if (!IsPrefixConsistent(node, p2.Base, LHS, fwd)) {
                    sConstr.Add(new IntEq(node.Env.ZeroInt, p2.Power));
                    return SimplifyResult.Proceed;
                }
            }

            if (SimplifyPower(node, fwd))
                continue;
            break;
        }
        return SimplifyResult.Proceed;
    }

    static int simplifyCount;

    protected override SimplifyResult SimplifyAndPropagateInternal(NielsenNode node, DetModifier sConstr, ref BacktrackReasons reason) {
        simplifyCount++;
        Log.WriteLine($"Simplify Eq ({simplifyCount}): {LHS} = {RHS}");
#if false
        lhs = LcpCompression(lhs) ?? lhs;
        rhs = LcpCompression(rhs) ?? rhs;
#endif
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
            while (eq.IsNonEmpty() && eq[true] is PowerToken p) {
                Str? s;
                if ((s = SimplifyPowerSingle(node, p)) is not null) {
                    eq = node.Env.StrManager.DropLeft(eq);
                    eq = node.Env.StrManager.Concat(eq, s);
                    continue;
                }
                break;
            }
            if (eq.IsEmpty())
                return SimplifyResult.Satisfied;
            if (SimplifyEmpty(eq.GetEnumerator(), node, sConstr) == SimplifyResult.Conflict) {
                reason = BacktrackReasons.SymbolClash;
                return SimplifyResult.Conflict;
            }
            LHS = eq;
            RHS = node.Env.EmptyStr;
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
        if (LHS is { Length: 1, First: StrVarToken s1 })
            AddDefinition(s1, RHS, node, sConstr);
        if (RHS is { Length: 1, First: StrVarToken s2 })
            AddDefinition(s2, LHS, node, sConstr);
        SortStr();
        return SimplifyResult.Proceed;
    }

    static NumCmpModifier? SplitPowerElim(StrToken t, Str s, Environment env, bool dir) {
        if (t is not PowerToken p1)
            return null;
        var r = CommPower(p1.Base, s, env, dir);
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

    ModifierBase? SplitEq(bool dir, Environment env/*, Dictionary<NamedInt, PDD<BigRational>> intSubst*/) {
        if (LHS.IsEmpty() || RHS.IsEmpty())
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
        var lhsLen = LenVar.MkLenPoly([LHS[dir]], env);
        constDiff += lhsLen.ConstOffset;

        //len = LenVar.MkLenPoly([RHS[dir]], env);
        //PDD<BigRational> rhsLen = len.Apply(intSubst);
        var rhsLen = LenVar.MkLenPoly([RHS[dir]], env);
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
                t = LHS[dir, lhsIdx++];
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
                len = LenVar.MkLenPoly([t], env);
                //ratLen = len.Apply(intSubst);
                constDiff += len.ConstOffset;
                lhsLen = lhsLen.Add(len);
                continue;
            }
            if (RHS.Length <= rhsIdx)
                break;
            t = RHS[dir, rhsIdx++];
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
            len = LenVar.MkLenPoly([t], env);
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
                : new EqSplitModifier(this, (uint)bestLhs, (uint)bestRhs, (int)best, dir);
    }

#if false
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

    static void GetParikhCandidates(Str s, int from, int to, HashSet<List<StrToken>> pattern) {
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

    static HashSet<List<StrToken>> GetParikhCandidates(Str s) {
        HashSet<List<StrToken>> pattern = [];

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

        for (int i = 0; i < charIntervals.Count; i++) {
            (from, to) = charIntervals[i];
            GetParikhCandidates(s, from, to, pattern);
        }
        return pattern;
    }

    static void GroupParikh(Str s, List<StrToken> pattern, IDictionary<Str, int> patternOcc, ref int constant, int sig) {
        Debug.Assert(pattern.IsWord());
        Debug.Assert(pattern.Count > 1);

        Str? runningStr = null;
        int i = 0;

        while (i < s.Length) {
            // find the start of the gap
            int k;
            int j;
            while (i < s.Length) {
                j = 0;
                for (; i + j < s.Length && j < pattern.Count; j++) {
                    if (!s[i + j].Equals(pattern[j]))
                        break;
                }
                if (j >= pattern.Count) {
                    // we found a proper occurrence
                    constant += sig;
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
                runningStr = s.SubStr(i, j + 1);
                i += j + 1;
                break;
            }
            if (runningStr is null)
                break;

            // extend the gap (center case)
            while (i < s.Length) {
                if (s[i] is not CharToken) {
                    // consecutive non-variables; just add
                    runningStr.AddLast(s[i]);
                    i++;
                    continue;
                }
                j = GetNextNonChar(i, s);
                if (j - i >= pattern.Count || j >= s.Length)
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
            j = Math.Min(GetNextNonChar(i, s) - i, Math.Min(pattern.Count, (int)s.Length - i));
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
        Debug.Assert(i >= s.Length);
    }

    static int OverApprox(Str gap) {
        Debug.Assert(gap.IsNonEmpty());
        Debug.Assert(gap.Any(o => o is not CharToken));
        if (gap.Length == 1)
            return 0;
        int overApprox = 0;
        if (gap[0] is CharToken)
            overApprox++;
        if (gap[^1] is CharToken)
            overApprox++;
        return gap.Count(o => o is not CharToken) + overApprox - 1;

    }

    static bool CheckMultiSequenceParikh(Str s1, Str s2, List<StrToken> pattern) {
        Dictionary<Str, int> patternOcc = [];
        int constant = 0;
        GroupParikh(s1, pattern, patternOcc, ref constant, 1);
        GroupParikh(s2, pattern, patternOcc, ref constant, -1);

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
#endif

    static ModifierBase? SplitVarVar(Str s1, Str s2, bool dir) {
        if (s1.IsEmpty() || s2.IsEmpty() || s1[dir] is not StrVarToken v1 || s2[dir] is not StrVarToken v2)
            return null;
        return new VarNielsenModifier(v1, v2, dir);
    }

    ModifierBase? SplitGroundPower(StrToken t, Str s, Environment env, Dictionary<NamedStrToken, Dictionary<NamedStrToken, List<StrToken>>> varDep, bool dir) {
        if (t is not StrVarToken v || s.IsEmpty() || s[dir] is not UnitToken)
            return null;
        var p = TryGetPowerSplitBase(v, s, env, varDep, dir);
        return p.Count == 0 ? null : new GPowerIntrModifier(p, dir);
    }

    ModifierBase? SplitVarChar(StrToken t, Str s, bool dir) {
        if (t is not StrVarToken v || s.IsEmpty() || s[dir] is not UnitToken)
            return null;
        return new ConstNielsenModifier(v, s[dir], dir);
    }

    ModifierBase? SplitVarPower(StrToken t, Str s, bool dir) {
        if (t is not StrVarToken v || s.IsEmpty() || s[dir] is not PowerToken { Ground: true } p)
            return null;
        return new PowerSplitModifier(v, p, dir);
    }

    ModifierBase ExtendDir(Dictionary<NamedStrToken, Dictionary<NamedStrToken, List<StrToken>>> varDep, Environment env, Dictionary<NamedInt, PDD<BigRational>> intSubst, bool dir) {
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

        var t1 = LHS[dir];
        var t2 = RHS[dir];

        ModifierBase? ret;

        if ((ret = SplitPowerElim(t1, RHS, env, dir)) is not null)
            return ret;
        if ((ret = SplitPowerElim(t2, LHS, env, dir)) is not null)
            return ret;
        if (t2 is not NamedStrToken && (ret = SplitPowerUnwind(t1, false)) is not null)
            return ret;
        if (t1 is not NamedStrToken && (ret = SplitPowerUnwind(t2, false)) is not null)
            return ret;
        if ((ret = SplitGroundPower(t1, RHS, env, varDep, dir)) is not null)
            return ret;
        if ((ret = SplitGroundPower(t2, LHS, env, varDep, dir)) is not null)
            return ret;
        if ((ret = SplitEq(dir, env/*, intSubst*/)) is not null)
            return ret;
        if ((ret = SplitVarPower(t1, RHS, dir)) is not null)
            return ret;
        if ((ret = SplitVarPower(t2, LHS, dir)) is not null)
            return ret;
        if ((ret = SplitVarChar(t1, RHS, dir)) is not null)
            return ret;
        if ((ret = SplitVarChar(t2, LHS, dir)) is not null)
            return ret;
        if ((ret = SplitVarVar(LHS, RHS, dir)) is not null)
            return ret;
        if ((ret = SplitPowerUnwind(t1, true)) is not null)
            return ret;
        if ((ret = SplitPowerUnwind(t2, true)) is not null)
            return ret;
        throw new NotSupportedException();
    }

    static int extendCnt;

    public override ModifierBase Extend(NielsenNode node, Dictionary<NamedInt, PDD<BigRational>> intSubst) {
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

    public override StrConstraint Negate() => 
        new StrNonEq(LHS, RHS);

    public override BoolExpr ToExpr(NielsenGraph graph) {
        return graph.Ctx.MkEq(LHS.ToExpr(graph), RHS.ToExpr(graph));
    }

    public override int GetHashCode() => 
        HashCode.Combine(LHS.GetHashCode(), RHS.GetHashCode()) * 782620193;

    public override string ToString() => $"{LHS} = {RHS}";
}