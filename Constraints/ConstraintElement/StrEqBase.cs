using System.Diagnostics;
using StringBreaker.IntUtils;
using StringBreaker.Strings;
using StringBreaker.Strings.Tokens;

namespace StringBreaker.Constraints.ConstraintElement;

public abstract class StrEqBase : StrConstraint, IComparable<StrEqBase> {
    public StrRef LHS { get; protected set; }
    public StrRef RHS { get; protected set; }

    protected StrEqBase(NielsenContext ctx, StrRef lhs, StrRef rhs) {
        LHS = lhs;
        RHS = rhs;
        SortStr(ctx);
    }

    public override bool Equals(object? obj) => obj is StrEqBase other && Equals(other);
    public bool Equals(StrEqBase? other) => CompareTo(other) == 0;
    public override int GetHashCode() => HashCode.Combine(LHS, RHS, GetType());

    protected void SortStr(NielsenContext ctx) {
        StrRef s1 = LHS, s2 = RHS;
        SortStr(ctx, ref s1, ref s2, true);
        LHS = s1;
        RHS = s2;
    }

    protected static void SortStr(NielsenContext ctx, ref StrRef s1, ref StrRef s2, bool dir) {
        StrTokenRef? t1 = s1.Peek(ctx, dir);
        if (t1 is null)
            return;
        StrTokenRef? t2 = s2.Peek(ctx, dir);
        if (t2 is null) {
            (s1, s2) = (s2, s1);
            return;
        }

        if (StrToken.StrTokenOrder[t1.Token.GetType()] > StrToken.StrTokenOrder[t2.Token.GetType()])
            (s1, s2) = (s2, s1);
        Debug.Assert(StrToken.StrTokenOrder[t1.Token.GetType()] <= StrToken.StrTokenOrder[t2.Token.GetType()]);
    }

    // Given p^m and s=u_1 ... u_n
    // Counts the number of p in prefix of s (just shallow; does not count powers of powers)
    protected static (Poly num, int idx) CommPower(StrRef @base, StrRef s, bool dir) {
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
    }

    protected static bool SimplifySame(NielsenContext ctx, StrRef s1, StrRef s2, bool dir) {
        if (!s1.Peek2(ctx, dir).Equals(s2.Peek2(ctx, dir)))
            return false;
        Log.WriteLine("Simplify Eq: " + s1.Peek2(ctx, dir) + "; " + s2.Peek2(ctx, dir));
        s1.Skip(ctx, dir);
        s2.Skip(ctx, dir);
        return true;
    }

    protected static bool IsPrefixConsistent(NielsenContext ctx, StrRef s1, StrRef s2, bool dir) {
        int min = Math.Min(s1.Count, s2.Count);
        for (int i = 0; i < min; i++) {
            StrToken t1 = s1.Peek(ctx, dir, i).Token;
            StrToken t2 = s2.Peek(ctx, dir, i).Token;
            if (t1 is not UnitToken u1 || t2 is not UnitToken u2)
                // It might still be inconsistent, but it is harder to detect
                return true;
            if (ctx.AreDiseq(u1, u2))
                return false;
        }
        return true;
    }

    public static bool SimplifyPower(NielsenContext ctx, StrRef s1, StrRef s2, bool dir) {
        if (s1.Peek2(ctx, dir).Token is not PowerToken p1)
            return false;
        StrRef? s;
        if ((s = SimplifyPowerSingle(ctx, p1)) is not null) {
            s1.Skip(ctx, dir);
            s1.AddRange(s, dir);
            return true;
        }
        if (SimplifyPowerElim(ctx, p1, s1, s2, dir))
            return true;
        if (SimplifyPowerUnwind(ctx, p1, s1, dir))
            return true;
        if (s2.Peek2(dir).Token is PowerToken p2) {
            if ((s = SimplifyPowerSingle(ctx, p2)) is not null) {
                s2.Skip(dir);
                s2.AddRange(s, dir);
                return true;
            }
            if (SimplifyPowerElim(ctx, p2, s2, s1, dir))
                return true;
            if (SimplifyPowerUnwind(ctx, p2, s2, dir))
                return true;
        }
        return false;
    }

    static bool SimplifyPowerElim(NielsenContext ctx, PowerToken p, StrRef s1, StrRef s2, bool dir) {
        var r = CommPower(p.Base, s2, dir);
        if (r.idx <= 0)
            return false;
        if (ctx.IsLe(r.num, p.Power) || ctx.IsLt(r.num, p.Power)) {
            // r.num < p.Power
            s1.Skip(ctx, dir);
            for (var i = 0; i < r.idx; i++)
                s2.Skip(ctx, dir);
            var sub = p.Power.Clone();
            sub.Sub(r.num);
            s1.Add(new PowerToken(p.Base, sub), dir);
            Log.WriteLine("Simplify: power-elim " + p);
            return true;
        }
        if (ctx.IsLe(p.Power, r.num) || ctx.IsLt(p.Power, r.num)) {
            // p.Power <= r.num
            s1.Skip(ctx, dir);
            for (var i = 0; i < r.idx; i++)
                s2.Skip(ctx, dir);
            var sub = r.num.Clone();
            sub.Sub(p.Power);
            s2.Add(new PowerToken(p.Base, sub), dir);
            Log.WriteLine("Simplify: power-elim " + p);
            return true;
        }
        return false;
    }

    static bool SimplifyPowerUnwind(NielsenContext ctx, PowerToken p, StrRef s, bool dir) {
        if (!ctx.IsLt(new Poly(), p.Power))
            return false;

        Log.WriteLine("Simplify: >0-unwinding power " + s.Peek(ctx, dir));
        s.Skip(ctx, dir);
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
    protected static StrRef? SimplifyPowerSingle(NielsenContext ctx, PowerToken p) {
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
        if (ctx.IsPowerElim(p.Power)) {
            Log.WriteLine("Simplify: Drop 0-power " + p);
            return [];
        }
        // u^1 => u
        if (ctx.IsOne(p.Power)) {
            Log.WriteLine("Simplify: Resolve 1-power " + p);
            return p.Base;
        }

        // Don't unwind based on bounds!! (Not good for detecting similar powers!)
        // If at all only based on known powers!

        if (Options.ReasoningUnwindingBound > 1) {
            // Unwind based on options...
            var bounds = p.Power.GetBounds(ctx);
            if (bounds.IsUnit) {
                Debug.Assert(bounds.Min > 1);
                Log.WriteLine("Simplify: Resolve " + bounds.Min + "-power " + p);
                StrRef r = [];
                for (Len i = 0; i < bounds.Min; i++) {
                    r.AddLastRange(p.Base);
                }
                return r;
            }
        }

        // simplify((u^m v)^n) => (simplify(u^m) v)^n
        // Actually all, but not sure we need to apply it to all sub powers
        // (practical problem: We can only remove first/last element)
        List<StrRef?> partialList = [];
        bool has = false;
        for (int i = 0; i < p.Base.Count; i++) {
            StrRef? r = p.Base[i] is PowerToken p3 ? SimplifyPowerSingle(ctx, p3) : null;
            has |= r is not null;
            partialList.Add(r);
        }
        if (has) {
            StrRef r = [];
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
            return [new PowerToken(lcp, p.Power)];

#if false
        if (ctx.IsLt(new Poly(), p.Power)) {
            // Rotate it in the minimal order
            int idx = GetMinimalOrder(p.Base);
            StrRef r;
            if (idx != 0) {
                Poly newPower = p.Power.ShallowClone();
                newPower.Sub(1);
                StrRef oldBase = p.Base;
                StrRef newBase = p.Base.Rotate(idx);
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

            var bounds = p.Power.GetBounds(ctx);
            if (!bounds.Min.IsPos)
                // We might only know that Power > 0 from a constraint but not the bounds themselves...
                // however, it seems to be at least one so set it
                bounds = new Interval(1, bounds.Max);

            Poly power = p.Power.ShallowClone();
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
    // v' u^m u^n v'' => v' u^{m + n} v''
    // v' u^n u v'' => v' u^{n + 1} v''
    // v' u' (u'u'')^n u'' v' => v' (u'u'')^{n+1} v'
    // till fixed point
    public static StrRef? LcpCompression(StrRef s) {
        // Apply each at least once and then until the first one fails
        lcpCnt++;
#if DEBUG
        StrRef orig = s.ShallowClone();
#endif
        bool changed = false;
        StrRef? v = MergePowersRight(s);
        if (v is not null) {
            s = v;
            changed = true;
        }
        v = MergePowersLeft(s);
        if (v is null) {
#if DEBUG
            Log.WriteLine($"lcp ({lcpCnt}): {orig} => {(changed ? s : "fixed point")}");
#endif
            return changed ? s : null;
        }
        s = v;

        while (true) {
            v = MergePowersRight(s);
            if (v is null) {
#if DEBUG
                Log.WriteLine($"lcp ({lcpCnt}): {orig} => {s}");
#endif
                return s;
            }
            s = v;
            v = MergePowersLeft(s);
            if (v is null) {
#if DEBUG
                Log.WriteLine($"lcp ({lcpCnt}): {orig} => {s}");
#endif
                return s;
            }
            s = v;
        }
    }

    // v' u^m u^n v'' => v' u^{m + n} v''
    // v' u^n u v'' => v' u^{n + 1} v''
    static StrRef? MergePowersRight(StrRef s) {
        StrRef p = new(s.Count);
        Poly sum = new();
        StrRef b = [];
        Debug.Assert(sum.IsZero);

        // v' u^n u v'' => v' u^{n + 1} v''
        // Count how often this works
        int LookAhead(int pos) {
            int max = (s.Count - pos) / b.Count;
            int cnt = 0;
            for (; cnt < max; cnt++) {
                for (int j = 0; j < b.Count; j++) {
                    if (!b[j].Equals(s[pos + b.Count * cnt + j]))
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
                i += b.Count * cnt;
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
    static StrRef? MergePowersLeft(StrRef s) {

        // Find maximal u'' index
        // Return r: 0 <= r <= b.Count
        int LookAhead(StrRef b, int pos) {
            int max = Math.Min(s.Count, pos + b.Count);
            for (int i = pos; i < max; i++) {
                if (!s.Peek(false, i).Equals(b.Peek(false, i - pos)))
                    return pos - i;
            }
            return max - pos;
        }

        bool progress = false;
        StrRef r = new(s.Count);
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
                StrRef b = new(pow.Base.Count);
                for (int j = 0; j < idx; j++) {
                    b.AddFirst(pow.Base.Peek(true, pow.Base.Count - j - 1));
                    r.AddFirst(pow.Base.Peek(false, j));
                }
                for (int j = 0; j < pow.Base.Count - idx; j++) {
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
    }

    public override void Apply(Interpretation itp) {
        LHS = LHS.Apply(itp);
        RHS = RHS.Apply(itp);
    }

    public override void CollectSymbols(HashSet<NamedStrToken> vars, HashSet<SymCharToken> sChars, 
        HashSet<IntVar> iVars, HashSet<CharToken> alphabet) {
        LHS.CollectSymbols(vars, sChars, iVars, alphabet);
        RHS.CollectSymbols(vars, sChars, iVars, alphabet);
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
