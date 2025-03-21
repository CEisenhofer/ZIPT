using System.Diagnostics;
using Microsoft.Z3;
using StringBreaker.Constraints.Modifier;
using StringBreaker.IntUtils;
using StringBreaker.MiscUtils;
using StringBreaker.Tokens;

namespace StringBreaker.Constraints.ConstraintElement;

public sealed class StrEq : StrEqBase {

    public StrEq(Str lhs, Str rhs) : base(lhs, rhs) { }
    public StrEq(Str empty) : base([], empty) { }

    public override StrEq Clone() => 
        new(LHS.Clone(), RHS.Clone());

    // Given p^m and s=u_1 ... u_n
    // Counts the number of p in prefix of s (just shallow; does not count powers of powers)
    static (Poly num, int idx) CommPower(Str @base, Str s, bool dir) {
        Poly sum = new Poly();
        int pos = 0;
        Len offset = 0;
        Poly lastStableSum = sum;
        int lastStablePos = 0;
        int i = 0;

        for (; i < s.Count; i++) {
            var t = s.Peek(dir, i);
            if (pos == 0) {
                lastStablePos = i;
                lastStableSum = sum.Clone();
            }
            if (t.Equals(@base.Peek(dir, pos))) {
                pos++;
                if (pos >= @base.Count) {
                    Debug.Assert(pos == @base.Count);
                    pos = 0;
                    offset++;
                }
                continue;
            }
            if (t is PowerToken p2 && p2.Base.Equals(@base)) {
                sum.Plus(p2.Power);
                continue;
            }
            break;
        }
        if (pos == 0) {
            lastStablePos = i;
            lastStableSum = sum;
        }
        lastStableSum.Plus(offset);
        return (lastStableSum, lastStablePos);

#if false
        // TODO: Check soundness
        // TODO: Maybe no shifted occurrences
        var lastStableSum = sum;
        var lastStablePos = 0;
        int i = 0;
        for (; i < s.Count; i++) {
            if (pos == 0) {
                lastStablePos = i;
                lastStableSum = sum.Clone();
            }
            if (s[i].Equals(@base[pos])) {
                pos++;
                if (pos >= @base.Count) {
                    Debug.Assert(pos == @base.Count);
                    pos = 0;
                    offset++;
                }
                continue;
            }
            if (s[i] is PowerToken p2 && p2.Base.EqualsRotation(pos, @base)) {
                sum.Plus(p2.Power);
                continue;
            }
            break;
        }
        if (pos == 0) {
            lastStablePos = i;
            lastStableSum = sum;
        }
        lastStableSum.Plus(offset);
        return (lastStableSum, lastStablePos);
#endif
    }

    static bool SimplifyEq(Str s1, Str s2, bool dir) {
        if (!s1.Peek(dir).Equals(s2.Peek(dir)))
            return false;
        Log.WriteLine("Simplify Eq: " + s1.Peek(dir) + "; " + s2.Peek(dir));
        s1.Drop(dir);
        s2.Drop(dir);
        return true;
    }

    // Minimal order: The smallest token is front-most.
    // If there are multiple equal ones, the one after is smaller than all the ones in front of the other candidates and so on...
    // the order is always LHS to RHS (no matter in which direction we reduce)
    static int GetMinimalOrder(Str s) {

        StrToken LookAhead(int i, int l) => 
            s[(i + l) % s.Count];

        Debug.Assert(s.IsNonEmpty());
        List<int> candidates = Enumerable.Range(0, s.Count).ToList();
        List<int> newCandidates = [];

        for (int i = 0; candidates.Count != 1 && i < s.Count; i++) {
            StrToken min = LookAhead(candidates[0], i);
            newCandidates.Add(candidates[0]);
            Debug.Assert(candidates.IsNonEmpty());
            for (var j = 1; j < candidates.Count; j++) {
                var current = LookAhead(candidates[j], i);
                int cmp = min.CompareTo(current);
                switch (cmp) {
                    case 0:
                        newCandidates.Add(candidates[j]);
                        break;
                    case > 0:
                        newCandidates.Clear();
                        newCandidates.Add(candidates[j]);
                        min = current;
                        break;
                }
            }
            (newCandidates, candidates) = (candidates, newCandidates);
            newCandidates.Clear();
        }

        Debug.Assert(candidates.IsNonEmpty()); // this can be violated if we have e.g., (aa)^n but this should be simplified away anyway...
        return candidates[0];
    }

    // Simplify the power standalone
    // (u^m)^n => u^{mn}
    // ""^n => ""
    // u^0 => ""
    // u^1 => u
    // (u_1 ... u_k)^n => u_1 ... u_l (u_{l+1} ... u_l)^{n - 1} u_{l+1} ... u_k with u_{l+1} ... u_l being the minimal ordering 
    // Only if the previous is already in the desired normal form:
    // u^i => u...u [l times, where l is the lower bound of i] - maybe not a good idea, but not sure [option?]
    // The direction is there to decide in which direction to unwind
    // u^n => uu^{n - 1} vs u^{n - 1}u
    static Str? SimplifyPowerSingle(NielsenNode node, PowerToken p, bool dir) {
        Debug.Assert(!p.Power.IsConst(out var dl) || !dl.IsNeg);
        if (p.Base is [PowerToken p2])
            // (u^m)^n => u^{mn}
            return [new PowerToken(p2.Base, Poly.Mul(p.Power, p2.Power))];

        // ""^n => ""
        if (p.Base.IsEmpty()) {
            Log.WriteLine("Simplify: Resolve empty-power " + p);
            return [];
        }
        // u^0 => ""
        if (node.IsZero(p.Power)) {
            Log.WriteLine("Simplify: Drop 0-power " + p);
            return [];
        }
        // u^1 => u
        if (node.IsOne(p.Power)) {
            Log.WriteLine("Simplify: Resolve 1-power " + p);
            return p.Base;
        }

        // Don't unwind based on bounds!! (Not good for detecting similar powers!)
        // If at all only based on known powers!

        if (Options.ReasoningUnwindingBound > 1) {
            // Unwind based on options...
            var bounds = p.Power.GetBounds(node);
            if (bounds.IsUnit) {
                Debug.Assert(bounds.Min > 1);
                Log.WriteLine("Simplify: Resolve " + bounds.Min + "-power " + p);
                Str r = [];
                for (Len i = 0; i < bounds.Min; i++) {
                    r.AddLastRange(p.Base);
                }
                return r;
            }
        }

        // simplify((u^m v)^n) => (simplify(u^m) v)^n
        // Actually all, but not sure we need to apply it to all sub powers
        // (practical problem: We can only remove first/last element)
        List<Str?> partialList = [];
        bool has = false;
        for (int i = 0; i < p.Base.Count; i++) {
            Str? r = p.Base[i] is PowerToken p3 ? SimplifyPowerSingle(node, p3, dir) : null;
            has |= r is not null;
            partialList.Add(r);
        }
        if (has) {
            Str r = [];
            for (int i = 0; i < partialList.Count; i++) {
                if (partialList[i] is { } t2)
                    r.AddLastRange(t2);
                else
                    r.AddLast(p.Base[i]);
            }
            Debug.Assert(partialList.Any(o => o is not null));
            return [new PowerToken(r, p.Power)];
        }
        var lcp = LcpCompression(p.Base);
        if (lcp is not null)
            return lcp;

#if false
        if (node.IsLt(new Poly(), p.Power)) {
            // Rotate it in the minimal order
            int idx = GetMinimalOrder(p.Base);
            Str r;
            if (idx != 0) {
                Poly newPower = p.Power.Clone();
                newPower.Sub(1);
                Str oldBase = p.Base;
                Str newBase = p.Base.Rotate(idx);
                p = new PowerToken(newBase, newPower);
                r = [];
                if (dir) {
                    for (int i = oldBase.Count; i > idx; i--) {
                        r.Add(oldBase[i - 1], true);
                    }
                    r.Add(p, true);
                    for (int i = idx; i > 0; i--) {
                        r.Add(oldBase[i - 1], true);
                    }
                }
                else {
                    for (int i = 0; i < idx; i++) {
                        r.Add(oldBase[i], false);
                    }
                    r.Add(p, false);
                    for (int i = idx; i < oldBase.Count; i++) {
                        r.Add(oldBase[i], false);
                    }
                }
                return r;
            }

            var bounds = p.Power.GetBounds(node);
            if (!bounds.Min.IsPos)
                // We might only know that Power > 0 from a constraint but not the bounds themselves...
                // however, it seems to be at least one so set it
                bounds = new Interval(1, bounds.Max);

            Poly power = p.Power.Clone();
            power.Sub(bounds.Min);
            r = [];
            for (Len i = 0; i < bounds.Min; i++) {
                r.AddRange(p.Base, !dir);
            }
            r.Add(new PowerToken(p.Base, power), !dir);
            return r;
        }
#endif
        return null;
    }

    static bool SimplifyPower(NielsenNode node, Str s1, Str s2, bool dir) {
        if (s1.Peek(dir) is not PowerToken p1)
            return false;
        Str? s;
        if ((s = SimplifyPowerSingle(node, p1, dir)) is not null) {
            s1.Drop(dir);
            s1.AddRange(s, dir);
            return true;
        }
        if (SimplifyPowerElim(node, p1, s1, s2, dir))
            return true;
        if (SimplifyPowerUnwind(node, p1, s1, dir))
            return true;
        if (s2.Peek(dir) is PowerToken p2) {
            if ((s = SimplifyPowerSingle(node, p2, dir)) is not null) {
                s2.Drop(dir);
                s2.AddRange(s, dir);
                return true;
            }
            if (SimplifyPowerElim(node, p2, s2, s1, dir))
                return true;
            if (SimplifyPowerUnwind(node, p2, s2, dir))
                return true;
        }
        return false;
    }

    static bool SimplifyPowerElim(NielsenNode node, PowerToken p, Str s1, Str s2, bool dir) {
        var r = CommPower(p.Base, s2, dir);
        if (r.idx <= 0) 
            return false;
        if (node.IsLe(r.num, p.Power) || node.IsLt(r.num, p.Power)) {
            // r.num < p.Power
            s1.Drop(dir);
            for (var i = 0; i < r.idx; i++)
                s2.Drop(dir);
            var sub = p.Power.Clone();
            sub.Sub(r.num);
            s1.Add(new PowerToken(p.Base, sub), dir);
            Log.WriteLine("Simplify: power-elim " + p);
            return true;
        }
        if (node.IsLe(p.Power, r.num) || node.IsLt(p.Power, r.num)) {
            // p.Power <= r.num
            s1.Drop(dir);
            for (var i = 0; i < r.idx; i++)
                s2.Drop(dir);
            var sub = r.num.Clone();
            sub.Sub(p.Power);
            s2.Add(new PowerToken(p.Base, sub), dir);
            Log.WriteLine("Simplify: power-elim " + p);
            return true;
        }
        return false;
    }

    static bool SimplifyPowerUnwind(NielsenNode node, PowerToken p, Str s, bool dir) {
        if (!node.IsPowerElim(p.Power))
            return false;

        Log.WriteLine("Simplify: >0-unwinding power " + s.Peek(dir));
        s.Drop(dir);
        var sub = p.Power.Clone();
        sub.Sub(1);
        s.Add(new PowerToken(p.Base, sub), dir);
        s.AddRange(p.Base, dir);
        return true;
    }

    SimplifyResult SimplifyDir(NielsenNode node, List<Subst> newSubst, bool dir) {
        var s1 = LHS;
        var s2 = RHS;
        SortStr(ref s1, ref s2, dir);
        while (LHS.IsNonEmpty() && RHS.IsNonEmpty()) {
            SortStr(ref s1, ref s2, dir);
            Debug.Assert(s1.Count > 0);
            Debug.Assert(s2.Count > 0);

            if (SimplifyEq(s1, s2, dir))
                continue;

            if (s1.Peek(dir) is CharToken && s2.Peek(dir) is CharToken)
                return SimplifyResult.Conflict;

            if (s1.Peek(dir) is SymCharToken sc1) {
                if (s2.Peek(dir) is UnitToken u) {
                    newSubst.Add(new SubstSChar(sc1, u));
                    return SimplifyResult.Proceed;
                }
            }

            LHS = LcpCompression(s1) ?? s1;
            RHS = LcpCompression(s2) ?? s2;
            s1 = LHS;
            s2 = RHS;
            SortStr(ref s1, ref s2, dir);

            if (SimplifyPower(node, s1, s2, dir))
                continue;
            break;
        }
        return SimplifyResult.Proceed;
    }

    // We apply the following steps:
    // v' u^m u^n v'' => v' u^{m + n} v''
    // v' u^n u v'' => v' u^{n + 1} v''
    // v' u' (u'u'')^n u'' v' => v' (u'u'')^{n+1} v'
    // till fixed point
    public static Str? LcpCompression(Str s) {
        // Apply each at least once and then until the first one fails
        bool changed = false;
        Str? v = MergeExistingPowers(s);
        if (v is not null) {
            s = v;
            changed = true;
        }
        v = MergeNewPowers(s);
        if (v is null)
            return changed ? s : null;
        s = v;

        while (true) {
            v = MergeExistingPowers(s);
            if (v is null)
                return s;
            s = v;
            v = MergeNewPowers(s);
            if (v is null)
                return s;
            s = v;
        }
    }

    // v' u^m u^n v'' => v' u^{m + n} v''
    // v' u^n u v'' => v' u^{n + 1} v''
    static Str? MergeExistingPowers(Str s) {
        // TODO: Optimize like MergeNewPowers
        Str p = new(s.Count);
        Poly sum = new();
        Str b = [];
        Debug.Assert(sum.IsZero);

        // v' u^n u v'' => v' u^{n + 1} v''
        // Count how often this works
        int LookAhead(int pos) {
            int max = (s.Count - pos) / b.Count;
            int cnt = 0;
            for (; cnt < max; cnt++) {
                for (int j = 0; j < b.Count; j++) {
                    if (!b[j].Equals(b[pos + b.Count * cnt + j]))
                        return cnt;
                }
            }
            return cnt;
        }

        bool compressed = false;
        for (int i = 0; i < s.Count; i++) {
            if (s[i] is not PowerToken pow) {
                if (!sum.IsZero) {
                    Debug.Assert(b.IsNonEmpty());
                    p.AddLast(new PowerToken(b, sum));
                }
                b = [];
                sum = new Poly();
                p.AddLast(s[i]);
                continue;
            }
            if (!pow.Base.Equals(b)) {
                if (!sum.IsZero) {
                    Debug.Assert(b.IsNonEmpty());
                    p.AddLast(new PowerToken(b, sum));
                }
                b = pow.Base;
                sum = pow.Power.Clone();
                int cnt = LookAhead(i + 1);
                compressed = true;
                i += b.Count * cnt;
                sum.Plus(cnt);
                continue;
            }
            compressed = true;
            sum.Plus(pow.Power);
        }
        if (!sum.IsZero) {
            Debug.Assert(b.IsNonEmpty());
            p.AddLast(new PowerToken(b, sum));
        }
        return compressed ? p : null;
    }

    // v' u'' (u'u'')^n v' => v' (u''u')^{n+1} u'' v'
    // We traverse the sequence backwards.
    // If we encounter (u'u'')^n we traverse u'u'' backwards and check how long it works after the power
    static Str? MergeNewPowers(Str s) {

        // Find maximal u'' index
        // Return r: 0 <= r <= b.Count
        int LookAhead(Str b, int pos) {
            int max = Math.Min(s.Count, pos + b.Count);
            for (int i = pos; i < max; i++) {
                if (!s.Peek(false, pos).Equals(b.Peek(false, i - pos)))
                    return pos - i;
            }
            return max - pos;
        }

        bool progress = false;
        Str r = new(s.Count);
        for (int i = 0; i < s.Count; i++) {
            var c = s.Peek(false, i);
            if (c is not PowerToken pow) {
                r.AddFirst(c);
                continue;
            }
            int cnt = 0;
            int idx;
            while ((idx = LookAhead(pow.Base, i + 1 + cnt * pow.Base.Count)) == pow.Base.Count) {
                // This only happens in case u' = ""
                cnt++;
            }
            if (cnt > 0) {
                Poly p = pow.Power.Clone();
                p.Plus(cnt);
                r.AddFirst(new PowerToken(pow.Base, p));
                i += cnt * pow.Base.Count;
                progress = true;
            }
            else if (idx > 0) {
                i += idx;
                Str b = new(pow.Base.Count);
                for (int j = 0; j < idx; j++) {
                    b.AddFirst(pow.Base.Peek(false, j));
                }
                for (int j = 0; j < b.Count; j++) {
                    b.AddLast(pow.Base.Peek(false, j));
                }
                r.AddFirst(new PowerToken(b, pow.Power));
                progress = true;
            }
            else
                r.AddFirst(pow);
        }
        return progress ? r : null;
    }

    static SimplifyResult SimplifyEmpty(IEnumerable<StrToken> s, NielsenNode node, List<Subst> newSubst, HashSet<Constraint> newSideConstr) {
        foreach (var t in s) {
            if (t is UnitToken)
                return SimplifyResult.Conflict;
            if (t is StrVarToken v)
                newSubst.Add(new SubstVar(v));
            else if (t is PowerToken p) {
                if (node.IsLt(new Poly(), p.Power))
                    // p.Power > 0
                    newSideConstr.Add(new StrEq(p.Base));
                else if (!p.Base.IsNullable(node))
                    // p.Base != ""
                    newSideConstr.Add(new IntEq(p.Power));
            }
            else
                throw new NotSupportedException();
        }
        return SimplifyResult.Proceed;
    }

    // Try to add the substitution: x / s ==> do an occurrence check. If it fails, we have to add it as an ordinary equation
    public void AddDefinition(StrVarToken v, Str s, NielsenNode node, List<Subst> newSubst, HashSet<Constraint> newSideConstr) {
        if (s.RecursiveIn(v))
            // newSideConstr.Add(new StrEq([v], s));
            return;
        newSubst.Add(new SubstVar(v, s));
    }

    static int simplifyCount;

    protected override SimplifyResult SimplifyInternal(NielsenNode node, 
        List<Subst> newSubst, HashSet<Constraint> newSideConstr, 
        ref BacktrackReasons reason) {
        simplifyCount++;
        Log.WriteLine("Simplify Eq (" + simplifyCount + "): " + LHS + " = " + RHS);
        if (SimplifyDir(node, newSubst, true) == SimplifyResult.Conflict) {
            reason = BacktrackReasons.SymbolClash;
            return SimplifyResult.Conflict;
        }
        if (SimplifyDir(node, newSubst, false) == SimplifyResult.Conflict) {
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
                if ((s = SimplifyPowerSingle(node, p, true)) is not null) {
                    eq.Drop(true);
                    eq.AddRange(s, true);
                    continue;
                }
                break;
            }
            if (eq.IsEmpty())
                return SimplifyResult.Satisfied;
            if (SimplifyEmpty(eq, node, newSubst, newSideConstr) == SimplifyResult.Conflict) {
                reason = BacktrackReasons.SymbolClash;
                return SimplifyResult.Conflict;
            }
            SortStr();
            return SimplifyResult.Proceed;
        }

        // TODO: Generalize for powers!
        // Check Multiset abstraction
        var lhsSet = LHS.ToSet();
        var rhsSet = RHS.ToSet();
        MSet<StrToken>.ElimCommon(lhsSet, rhsSet);
        if (lhsSet.IsEmpty() != rhsSet.IsEmpty()) {
            var nonEmpty = lhsSet.IsEmpty() ? rhsSet : lhsSet;
            // Remove powers that actually do not exist anymore
            while (nonEmpty.IsNonEmpty() && nonEmpty.First().t is PowerToken p) {
                Str? s;
                if ((s = SimplifyPowerSingle(node, p, true)) is not null) {
                    nonEmpty.RemoveAll(p);
                    nonEmpty.Add(s);
                    continue;
                }
                break;
            }
            if (SimplifyEmpty(nonEmpty.Keys, node, newSubst, newSideConstr) == SimplifyResult.Conflict) {
                reason = BacktrackReasons.ParikhImage;
                return SimplifyResult.Conflict;
            }
            SortStr();
            return SimplifyResult.Proceed;
        }
        // Propagate assignments

        if (LHS is [StrVarToken] || RHS is [StrVarToken]) {
            var (v, s) = LHS is [StrVarToken] ? ((StrVarToken)LHS[0], RHS) : ((StrVarToken)RHS[0], LHS);
            // important: clone it; otherwise one might into endless recursions when applied to itself
            AddDefinition(v, s, node, newSubst, newSideConstr);
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

    NumUnwindingModifier? SplitPowerUnwind(StrToken t) => 
        t is not PowerToken p ? null : new NumUnwindingModifier(p.Power);

    Str? TryGetPowerSplitBase(StrVarToken v, Str s, bool dir) {
        if (s.IsEmpty())
            return null;
        var i = 0;
        for (; i < s.Count && !s.Peek(dir, i).Equals(v); i++) { }

        if (i >= s.Count)
            // Non-rec Case
            return null;
        // Rec Case
        Debug.Assert(s.Peek(dir, i).Equals(v));
        return dir 
            ? new Str(s.Take(i).ToList()) 
            : new Str(s.Reverse().Take(i).Reverse().ToList());
    }

    ModifierBase? SplitEq(Str s1, Str s2, bool dir) {
        if (s1.IsEmpty() || s2.IsEmpty())
            return null;
        // TODO: This is not optimal!
        Len constDiff = 0;
        Len best = Len.PosInf;
        int bestLhs = 0, bestRhs = 0;
        Poly lhs = new(), rhs = new();
        int lhsIdx = 0; int rhsIdx = 0;
        while (lhsIdx < s1.Count || rhsIdx < s2.Count) {
            if (lhsIdx > 0 || rhsIdx > 0) {
                if (lhs.IsZero && rhs.IsZero) {
                    if (constDiff.Abs() < best) {
                        best = constDiff;
                        bestLhs = lhsIdx;
                        bestRhs = rhsIdx;
                    }
                    if (constDiff.IsZero)
                        return new EqSplitModifier(this, bestLhs, bestRhs, dir);
                }
            }
            Poly len;
            if (lhs.IsEmpty() && rhs.IsNonEmpty() ||
                (lhs.IsEmpty() && rhs.IsEmpty() && constDiff.IsNeg)) {

                if (s1.Count <= lhsIdx)
                    break;
                len = LenVar.MkLenPoly([s1.Peek(dir, lhsIdx++)]);
                constDiff += len.ConstPart;
                len.ElimConst();
                if (!len.IsZero) {
                    lhs.Plus(len);
                    Poly.ElimCommon(lhs, rhs);
                }
                continue;
            }
            if (s2.Count <= rhsIdx)
                break;
            len = LenVar.MkLenPoly([s2.Peek(dir, rhsIdx++)]);
            constDiff -= len.ConstPart;
            len.ElimConst();
            if (!len.IsZero) {
                rhs.Plus(len);
                Poly.ElimCommon(lhs, rhs);
            }
        }
        if (best.IsInf)
            return null;
        Debug.Assert(!best.IsZero);
        if (best.IsNeg) {
            // split left
            if (bestLhs <= 0 || bestLhs >= s1.Count || s1.Peek(dir, bestLhs) is not StrVarToken v1 || !best.TryGetInt(out int val1))
                return null;
            return new VarPaddingModifier(v1, -val1, dir);
        }
        if (bestRhs <= 0 || bestRhs>= s2.Count || s2.Peek(dir, bestRhs) is not StrVarToken v2 || !best.TryGetInt(out int val2))
            return null;
        return new VarPaddingModifier(v2, val2, dir);
    }

    ModifierBase? SplitVarVar(Str s1, Str s2, bool dir) {
        if (s1.IsEmpty() || s2.IsEmpty() || s1.Peek(dir) is not StrVarToken v1 || s2.Peek(dir) is not StrVarToken v2)
            return null;

        Str? p1 = TryGetPowerSplitBase(v1, s2, dir);
        Str? p2 = TryGetPowerSplitBase(v2, s1, dir);
        if (p1 is not null && p2 is not null) {
            if (p1.Ground && p2.Ground) {
                Debug.Assert(false); // How could that happen?!
                return new GPowerGPowerIntrModifier(v1, v2, p1, p2, dir);
            }
            if (p1.Ground)
                return new CombinedModifier(
                    new GPowerIntrModifier(v1, p1, dir),
                    new ConstNielsenModifier(v2, v1, dir)
                );
            //return new GPowerPowerIntrModifier(v1, v2, p1, p2, dir);
            if (p2.Ground)
                return new CombinedModifier(
                    new GPowerIntrModifier(v2, p2, dir),
                    new ConstNielsenModifier(v1, v2, dir)
                );
            // return new GPowerPowerIntrModifier(v2, v1, p2, p1, dir);
            return
                new VarNielsenModifier(v1, v2, dir);
            //return new PowerPowerIntrModifier(v1, v2, p1, p2, dir);
        }
        if (p1 is not null) {
            (p1, p2) = (p2, p1);
            (v1, v2) = (v2, v1);
            (s1, s2) = (s2, s1);
        }
        if (p1 is null)
            return new VarNielsenModifier(v1, v2, dir);
        if (p1.Ground)
            return new GPowerIntrConstNielsen(v1, v2, p1, dir);
        return new PowerIntrConstNielsen(v1, v2, p1, dir);
    }

    ModifierBase? SplitVarChar(StrToken t, Str s, bool dir) {
        if (t is not StrVarToken v || s.IsEmpty() || s.Peek(dir) is not UnitToken)
            return null;
        Str? p = TryGetPowerSplitBase(v, s, dir);
        if (p is null)
            return new ConstNielsenModifier(v, s.Peek(dir), dir);
        if (p.Ground)
            return new GPowerIntrModifier(v, p, dir);
        return new ConstNielsenModifier(v, s.Peek(dir), dir);
        //return new PowerIntrModifier(v, p, dir);
    }

    ModifierBase? SplitVarPower(StrToken t, Str s, bool dir) {
        if (t is not StrVarToken v || s.IsEmpty() || s.Peek(dir) is not PowerToken { Ground: true } p)
            return null;
        throw new NotImplementedException();
    }

    ModifierBase ExtendDir(bool dir) {
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
        if (t2 is not StrVarToken && (ret = SplitPowerUnwind(t1)) is not null)
            return ret;
        if (t1 is not StrVarToken && (ret = SplitPowerUnwind(t2)) is not null)
            return ret;
        if ((ret = SplitEq(s1, s2, dir)) is not null)
            return ret;
        if ((ret = SplitVarChar(t1, s2, dir)) is not null)
            return ret;
        if ((ret = SplitVarChar(t2, s1, dir)) is not null)
            return ret;
        if ((ret = SplitVarVar(s1, s2, dir)) is not null)
            return ret;
        if ((ret = SplitVarPower(t1, s2, dir)) is not null)
            return ret;
        if ((ret = SplitVarPower(t2, s1, dir)) is not null)
            return ret;
        if ((ret = SplitPowerUnwind(t1)) is not null)
            return ret;
        if ((ret = SplitPowerUnwind(t2)) is not null)
            return ret;
        throw new NotSupportedException();
    }

    public override ModifierBase Extend(NielsenNode node) {
        var m1 = ExtendDir(true);
        var m2 = ExtendDir(false);
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
        new StrNonEq(LHS, RHS);

    public override BoolExpr ToExpr(NielsenGraph graph) {
        return graph.Ctx.MkEq(LHS.ToExpr(graph), RHS.ToExpr(graph));
    }

    public override int GetHashCode() {
        return 613461011 + LHS.GetHashCode() + 967118167 * RHS.GetHashCode();
    }

    public override string ToString() {
        return $"{LHS} = {RHS}";
    }

}