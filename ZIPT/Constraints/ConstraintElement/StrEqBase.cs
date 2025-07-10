using System.ComponentModel;
using System.Diagnostics;
using ZIPT.IntUtils;
using ZIPT.Tokens;

namespace ZIPT.Constraints.ConstraintElement;

public abstract class StrEqBase : StrConstraint, IComparable<StrEqBase> {
    public IStr LHS { get; protected set; }
    public IStr RHS { get; protected set; }

    protected StrEqBase(IStr lhs, IStr rhs) {
        LHS = lhs;
        RHS = rhs;
        SortStr();
    }

    public override bool Equals(object? obj) => obj is StrEqBase other && Equals(other);
    public bool Equals(StrEqBase? other) => CompareTo(other) == 0;
    public override int GetHashCode() => HashCode.Combine(LHS, RHS);

    protected void SortStr() {
        IStr s1 = LHS, s2 = RHS;
        uint i1 = 0, i2 = 0;
        SortStr(ref s1, ref i1, ref s2, ref i2, true);
        LHS = s1;
        RHS = s2;
    }

    protected static void SortStr(ref IStr s1, ref uint i1, ref IStr s2, ref uint i2, bool dir) {
        if (s1.IsEmpty())
            return;
        if (s2.IsEmpty()) {
            (s1, s2) = (s2, s1);
            (i1, i2) = (i2, i1);
			return;
        }
        Debug.Assert(s1.Length > 0);
        Debug.Assert(s2.Length > 0);

        if (StrToken.StrTokenOrder[s1.Peek(dir).GetType()] > StrToken.StrTokenOrder[s2.Peek(dir).GetType()]) {
            (s1, s2) = (s2, s1);
            (i1, i2) = (i2, i1);
		}
        Debug.Assert(StrToken.StrTokenOrder[s1.Peek(dir).GetType()] <= StrToken.StrTokenOrder[s2.Peek(dir).GetType()]);
    }

    // TODO: u'(u''u')^n u'' for u''u' count as n + 1 for u''u'
    // Given p^m and s=u_1 ... u_n
    // Counts the number of p in prefix of s (just shallow; does not count powers of powers)
    protected static (IntPoly num, int idx) CommPower(IStr @base, IStr s, bool dir) {
        IntPoly sum = new IntPoly();
        int pos = 0;
        IntPoly lastStableSum = sum;
        int lastStablePos = 0;
        int i = 0;

        for (; i < s.Length; i++) {
            var t = s.Peek(dir, i);
            if (pos == 0) {
                lastStablePos = i;
                lastStableSum = sum.Clone();
            }
            if (t.Equals(@base.Peek(dir, pos))) {
                pos++;
                if (pos >= @base.Length) {
                    Debug.Assert(pos == @base.Length);
                    pos = 0;
                    sum.Plus(1);
                }
                continue;
            }
            if (t is PowerToken p2 &&
                (pos == 0
                    ? p2.Base.Equals(@base)
                    : p2.Base.RotationEquals(@base, dir ? pos : (@base.Length - pos)))) {
                // We might not keep this if it is shifted and we do not find a pos == 0 afterwards
                sum.Plus(p2.Power);
                continue;
            }
            break;
        }
        if (pos == 0) {
            lastStablePos = i;
            lastStableSum = sum;
        }
        return (lastStableSum, lastStablePos);
    }

    protected static bool SimplifySame(IStr s1, ref uint i1, IStr s2, ref uint i2, bool dir) {
        if (!s1.Peek(dir).Equals(s2.Peek(dir)))
            return false;
        Log.WriteLine("Simplify Eq: " + s1.Peek(dir) + "; " + s2.Peek(dir));
        i1++;
        i2++;
        return true;
    }

    protected static bool IsPrefixConsistent(NielsenNode node, IStr s1, uint i1, IStr s2, uint i2, bool dir) {
        uint min = Math.Min(s1.Length - i1, s2.Length - i2);
        for (int i = 0; i < min; i++) {
            StrToken t1 = s1.Peek(dir, i);
            StrToken t2 = s2.Peek(dir, i);
            if (t1 is not UnitToken u1 || t2 is not UnitToken u2)
                // It might still be inconsistent, but it is harder to detect
                return true;
            if (node.AreDiseq(u1, u2))
                return false;
        }
        return true;
    }

    public static bool SimplifyPower(NielsenNode node, IStr s1, ref uint i1, IStr s2, ref uint i2, bool dir) {
        if (s1.Peek(dir) is not PowerToken p1)
            return false;
        IStr? s;
        if ((s = SimplifyPowerSingle(node, p1)) is not null) {
            s1.Drop(dir);
            i1++;
            s1.AddRange(s, dir);

            return true;
        }
        if (SimplifyPowerElim(node, p1, s1, s2, dir))
            return true;
        // Reason why we do not do unwinding in presence of a variable:
        // xb... = a^n... with n >= 1
        // implies x /ax but this can result in some int constraint bound propagate n >= 2
        // and result in a cycle as this makes a^n unwindable again
        // Instead we have to split on x / a^n x and x / a^m with 0 <= m < n
        if (s2.Peek(dir) is not NamedStrToken && SimplifyPowerUnwind(node, p1, s1, dir))
            return true;
        if (s2.Peek(dir) is PowerToken p2) {
            if ((s = SimplifyPowerSingle(node, p2)) is not null) {
                s2.Drop(dir);
                i2++;
                s2.AddRange(s, dir);
                return true;
            }
            if (SimplifyPowerElim(node, p2, s2, s1, dir))
                return true;
            if (s1.Peek(dir) is not NamedStrToken && SimplifyPowerUnwind(node, p2, s2, dir))
                return true;
        }
        return false;
    }

    static bool SimplifyPowerElim(NielsenNode node, PowerToken p, IStr s1, IStr s2, bool dir) {
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

    static bool SimplifyPowerUnwind(NielsenNode node, PowerToken p, IStr s, bool dir) {
        if (!node.IsLt(new IntPoly(), p.Power))
            return false;

        Log.WriteLine("Simplify: >0-unwinding power " + s.Peek(dir));
        s.Drop(dir);
        var sub = p.Power.Clone();
        sub.Sub(1);
        s.Add(new PowerToken(p.Base, sub), dir);
        s.AddRange(p.Base, dir);
        return true;
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
    protected static IStr? SimplifyPowerSingle(NielsenNode node, PowerToken p) {
        // This can be locally violated e.g., if some integer constraint simplified to 1 <= 0 so IsLt(1, 0) evaluates to true
        // Debug.Assert(!p.Power.IsConst(out var dl) || !dl.IsNeg);
        if (p.Power.IsConst(out var dl) && dl.IsNeg)
            // We could also just ignore it, but probably not worth making efforts simplifying it
            return null;

        if (p.Base is [PowerToken p2])
            // (u^m)^n => u^{mn}
            return [new PowerToken(p2.Base, IntPoly.Mul(p.Power, p2.Power))];

        // ""^n => ""
        if (p.Base.IsEmpty()) {
            Log.WriteLine("Simplify: Resolve empty-power " + p);
            return [];
        }
        // u^0 => ""
        if (node.IsPowerElim(p.Power)) {
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
                IStr r = [];
                for (BigIntInf i = 0; i < bounds.Min; i++) {
                    r.AddLastRange(p.Base);
                }
                return r;
            }
        }

        // simplify((u^m v)^n) => (simplify(u^m) v)^n
        // Actually all, but not sure we need to apply it to all sub powers
        // (practical problem: We can only remove first/last element)
        List<IStr?> partialList = [];
        bool has = false;
        for (int i = 0; i < p.Base.Length; i++) {
            IStr? r = p.Base[i] is PowerToken p3 ? SimplifyPowerSingle(node, p3) : null;
            has |= r is not null;
            partialList.Add(r);
        }
        if (has) {
            IStr r = [];
            for (int i = 0; i < partialList.Count; i++) {
                if (partialList[i] is { } t2)
                    r.AddLastRange(t2);
                else
                    r.AddLast(p.Base[i]);
            }
            Debug.Assert(partialList.Any(o => o is not null));
            return [new PowerToken(r, p.Power)];
        }
        var lcp = LcpCompressionFull(p.Base);
        if (lcp is not null)
            return [new PowerToken(lcp, p.Power)];

#if false
        if (node.IsLt(new Poly(), p.Power)) {
            // Rotate it in the minimal order
            int idx = GetMinimalOrder(p.Base);
            IStr r;
            if (idx != 0) {
                Poly newPower = p.Power.Clone();
                newPower.Sub(1);
                IStr oldBase = p.Base;
                IStr newBase = p.Base.Rotate(idx);
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

    static int lcpCnt;

    // We apply the following steps:
    // v'uu...uv'' => v' u^n v'' (only if singleCompress)
    // v' u^m u^n v'' => v' u^{m + n} v''
    // v' u^n u v'' => v' u^{n + 1} v''
    // v' u' (u'u'')^n u'' v' => v' (u'u'')^{n+1} v'
    // till fixed point
    public static IStr? LcpCompressionFull(IStr s) {
        if (s.Length < 2)
            return null;
#if DEBUG
        IStr orig = s.Clone();
#endif
        bool changed = false;
        while (MergeSingle(s) is { } v) {
            s = v;
            changed = true;
        }
        IStr? r = LcpCompression(s);

#if DEBUG
        Log.WriteLine($"lcp-full ({lcpCnt}): {orig} => {s}");
#endif

        if (r is not null)
            return r;
        return changed ? s : null;
    }

    // Everything from *Full but compressing non-power sequences into powers 
    // [Distinction, as introducing powers on top-level might not be beneficial]
    public static IStr? LcpCompression(IStr s) {
        if (s.Length < 2)
            return null;

        // Apply each at least once and then until the first one fails
        lcpCnt++;
#if DEBUG
        IStr orig = s.Clone();
#endif

        bool globalChanged = false;
        bool changed1 = true;
        bool changed2 = true;

        while (changed1 || changed2) {
            IStr? v = MergePowersRight(s);
            if (v is not null) {
                s = v;
                changed1 = true;
                globalChanged = true;
            }
            else
                changed1 = false;
            if (!changed1 && !changed2)
                break;
            v = MergePowersLeft(s);
            if (v is not null) {
                s = v;
                changed2 = true;
                globalChanged = true;
            }
            else
                changed2 = false;
        }
#if DEBUG
        Log.WriteLine($"lcp-short ({lcpCnt}): {orig} => {s}");
#endif
        return !globalChanged ? null : s;
    }

    // v'u...uv'' => v' u^n v'' (first only and preferring minimal compression: baaaab => b a^4 b rather than b (aa)^2 b)
    // u is ground
    // Implementation: Sliding window
    static IStr? MergeSingle(IStr s) {
        if (s.Length < 2)
            return null;
        int to = s.Length / 2;
        for (int i = 1; i <= to; i++) {
            for (int j = 0; j + 2 * i <= s.Length; j++) {
                int rep = 1;
                for (; j + (rep + 1) * i <= s.Length; rep++) {
                    bool failed = false;
                    for (int k = 0; k < i; k++) {
                        if (s[j + k] is NamedStrToken) {
                            // we want ground powers!
                            // break if we would compress a variable
                            failed = true;
                            break;
                        }
                        if (!s[j + k].Equals(s[j + rep * i + k])) {
                            failed = true;
                            break;
                        }
                    }
                    if (failed)
                        break;
                }
                if (rep > 1) {
                    IStr r = new(s.Length - rep * i + 1);
                    for (int k = 0; k < j; k++) {
                        r.AddLast(s[k]);
                    }
                    IStr b = new IStr(rep);
                    for (int k = 0; k < i; k++) {
                        b.AddLast(s[j + k]);
                    }
                    r.AddLast(new PowerToken(b, new IntPoly(rep)));
                    for (int k = j + rep * i; k < s.Length; k++) {
                        r.AddLast(s[k]);
                    }
                    Debug.Assert(r.Length == s.Length - rep * i + 1);
                    return r;
                }
            }
        }
        return null;
    }

    // v' u^m u^n v'' => v' u^{m + n} v''
    // v' u^n u v'' => v' u^{n + 1} v''
    static IStr? MergePowersRight(IStr s) {
        IStr p = new(s.Length);
        IntPoly sum = new();
        IStr b = [];
        Debug.Assert(sum.IsZero);

        // v' u^n u v'' => v' u^{n + 1} v''
        // Count how often this works
        int LookAhead(int pos) {
            int max = (s.Length - pos) / b.Length;
            int cnt = 0;
            for (; cnt < max; cnt++) {
                for (int j = 0; j < b.Length; j++) {
                    if (!b[j].Equals(s[pos + b.Length * cnt + j]))
                        return cnt;
                }
            }
            return cnt;
        }

        bool compressed = false;
        for (int i = 0; i < s.Length; i++) {
            if (s[i] is not PowerToken pow) {
                if (!sum.IsZero) {
                    Debug.Assert(b.IsNonEmpty());
                    p.AddLast(new PowerToken(b, sum));
                }
                b = [];
                sum = new IntPoly();
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
                i += b.Length * cnt;
                sum.Plus(cnt);
                compressed |= cnt > 0;
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
    static IStr? MergePowersLeft(IStr s) {

        // Find maximal u'' index
        // Return r: 0 <= r <= b.Count
        int LookAhead(IStr b, int pos) {
            int max = Math.Min(s.Length, pos + b.Length);
            for (int i = pos; i < max; i++) {
                if (!s.Peek(false, i).Equals(b.Peek(false, i - pos)))
                    return pos - i;
            }
            return max - pos;
        }

        bool progress = false;
        IStr r = new(s.Length);
        for (int i = 0; i < s.Length; i++) {
            var c = s.Peek(false, i);
            if (c is not PowerToken pow) {
                r.AddFirst(c);
                continue;
            }
            int cnt = 0;
            int idx;
            while ((idx = LookAhead(pow.Base, i + 1 + cnt * pow.Base.Length)) == pow.Base.Length) {
                // This only happens in case u' = ""
                cnt++;
            }
            if (cnt > 0) {
                IntPoly p = pow.Power.Clone();
                p.Plus(cnt);
                r.AddFirst(new PowerToken(pow.Base, p));
                i += cnt * pow.Base.Length;
                progress = true;
            }
            else if (idx > 0) {
                i += idx;
                IStr b = new(pow.Base.Length);
                for (int j = 0; j < idx; j++) {
                    b.AddFirst(pow.Base.Peek(true, pow.Base.Length - j - 1));
                    r.AddFirst(pow.Base.Peek(false, j));
                }
                for (int j = 0; j < pow.Base.Length - idx; j++) {
                    b.AddLast(pow.Base.Peek(true, j));
                }
                r.AddFirst(new PowerToken(b, pow.Power));
                progress = true;
            }
            else
                r.AddFirst(pow);
        }
        return progress ? r : null;
    }

    public override void Apply(Subst subst) {
        LHS = LHS.Apply(subst);
        RHS = RHS.Apply(subst);
        // Dependencies.Apply(subst);
    }

    public override void Apply(Interpretation itp) {
        LHS = LHS.Apply(itp);
        RHS = RHS.Apply(itp);
        // Dependencies.Apply(itp);
    }

    public override void CollectSymbols(NonTermSet nonTermSet, HashSet<CharToken> alphabet) {
        LHS.CollectSymbols(nonTermSet, alphabet);
        RHS.CollectSymbols(nonTermSet, alphabet);
    }

    public override bool Contains(NamedStrToken namedStrToken) =>
        LHS.Any(o => o.RecursiveIn(namedStrToken)) || RHS.Any(o => o.RecursiveIn(namedStrToken));

    public int CompareTo(StrEqBase? other) {
        if (other is null)
            return 1;
        int cmp = LHS.CompareTo(other.LHS);
        return cmp != 0 ? cmp : RHS.CompareTo(other.RHS);
    }

}
