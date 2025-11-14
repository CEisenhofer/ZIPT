using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.Numerics;
using System.Runtime.CompilerServices;
using ZIPT.Constraints.Modifier;
using ZIPT.IntUtils;
using ZIPT.Strings;
using ZIPT.Strings.Chunks;
using ZIPT.Strings.Tokens;

namespace ZIPT.Constraints.ConstraintElement;

public abstract class StrEqBase : StrConstraint, IComparable<StrEqBase> {

    Str lhs;
    Str rhs;

    public Str LHS
    {
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        get => lhs;
        protected set => lhs = value;
    }

    public Str RHS
    {
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        get => rhs;
        protected set => rhs = value;
    }

    public virtual bool Sorted => true;

    protected StrEqBase(Str lhs, Str rhs) {
        this.lhs = lhs;
        this.rhs = rhs;
        SortStr();
    }

    public override bool Equals(object? obj) => obj is StrEqBase other && Equals(other);
    public bool Equals(StrEqBase? other) => other is not null && GetType() == other.GetType() && CompareTo(other) == 0;
    public override int GetHashCode() => HashCode.Combine(LHS, RHS);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    protected void SortStr() {
        if (Sorted)
            SortStr(ref lhs, ref rhs, true);
    }

    // for just calling member functions always assuming we process left only

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    protected void SwpSides() => 
        (lhs, rhs) = (rhs, lhs);

    protected bool IsSorted(bool fwd = true) =>
        IsSorted(lhs, rhs, fwd);

    protected static bool IsSorted(Str s1, Str s2, bool fwd) {
        if (s1.IsEmpty())
            return true;
        if (s2.IsEmpty())
            return false;
        Debug.Assert(s1.Length > 0);
        Debug.Assert(s2.Length > 0);
        return s1.CompareTo(s2, fwd) <= 0;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    protected static void SortStr(ref Str s1, ref Str s2, bool fwd) {
        if (!IsSorted(s1, s2, fwd))
            (s1, s2) = (s2, s1);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    protected void SortStr(bool fwd) {
        Debug.Assert(Sorted);
        SortStr(ref lhs, ref rhs, fwd);
    }

    // TODO: u'(u''u')^n u'' for u''u' count as n + 1 for u''u'
    // Given p^m and s=u_1 ... u_n
    // Counts the number of p in prefix of s (just shallow; does not count powers of powers)
    protected static (PDD<BigInteger> num, int idx) CommPower(Str @base, Str s, Environment env, bool fwd) {
        PDD<BigInteger> sum = env.ZeroInt;
        uint pos = 0;
        PDD<BigInteger> lastStableSum = sum;
        int lastStablePos = 0;
        int i = 0;

        for (; i < s.Length; i++) {
            var t = s[fwd, i];
            if (pos == 0) {
                lastStablePos = i;
                lastStableSum = sum;
            }
            if (t.Equals(@base[fwd, pos])) {
                pos++;
                if (pos >= @base.Length) {
                    Debug.Assert(pos == @base.Length);
                    pos = 0;
                    sum = sum.Add(BigInteger.One);
                }
                continue;
            }
            if (t is PowerToken p2 &&
                (pos == 0
                    ? p2.Base.Equals(@base)
                    : p2.Base.RotationEquals(@base, fwd ? pos : (@base.Length - pos)))) {
                // We might not keep this if it is shifted and we do not find a pos == 0 afterwards
                sum = sum.Add(p2.Power);
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

    protected bool SimplifySame(Environment env, bool fwd) {
        if (!lhs[fwd].Equals(rhs[fwd]))
            return false;
        if (!lhs[fwd].RegexFree)
            // !!  a*u = a*v  =/>  u = v  !!
            return false;
        Log.WriteLine("Simplify Eq: " + lhs[fwd] + "; " + rhs[fwd]);
        lhs = env.StrManager.Drop(lhs, fwd);
        rhs = env.StrManager.Drop(rhs, fwd);
        return true;
    }

    protected static bool IsPrefixConsistent(NielsenNode node, Str s1, Str s2, bool fwd) {
        uint min = Math.Min(s1.Length, s2.Length);
        for (int i = 0; i < min; i++) {
            StrToken t1 = s1[fwd, i];
            StrToken t2 = s2[fwd, i];
            if (t1 is not CharToken c1 || t2 is not CharToken c2)
                // It might still be inconsistent, but it is harder to detect
                return true;
            if (!c1.Equals(c2))
                return false;
        }
        return true;
    }

    protected static SimplifyResult SimplifyEmpty(IEnumerable<StrToken> s, NielsenNode node, DetModifier constr) {
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

    public bool SimplifyPower(LocalInfo info, bool fwd) {
        Debug.Assert(Sorted);
        if (SimplifyPowerSide(info, fwd))
            return true;
        SwpSides();
        bool elim = SimplifyPowerSide(info, fwd);
        SwpSides();
        return elim;
    }

    public bool SimplifyPowerSide(LocalInfo info, bool fwd) {
        if (lhs[fwd] is not PowerToken p)
            return false;
        Str? s;
        if ((s = SimplifyPowerSingle(info, p)) is not null) {
            lhs = info.Env.StrManager.Concat(s, info.Env.StrManager.Drop(lhs, fwd), fwd);
            return true;
        }
        if (SimplifyPowerElim(info.CurrentNode, p, fwd))
            return true;
        // Reason why we do not do unwinding in presence of a variable:
        // xb... = a^n... with n >= 1
        // implies x /ax but this can result in some int constraint bound propagate n >= 2
        // and result in a cycle as this makes a^n unwindable again
        // Instead we have to split on x / a^n x and x / a^m with 0 <= m < n
        return rhs[fwd] is not NamedStrToken && SimplifyPowerUnwind(info.CurrentNode, p, fwd);
    }

    bool SimplifyPowerElim(NielsenNode node, PowerToken p, bool fwd) {
        Debug.Assert(ReferenceEquals(lhs[fwd], p));
        var r = CommPower(p.Base, rhs, node.Env, fwd);
        if (r.idx <= 0)
            return false;
        if (node.IsLe(r.num, p.Power) || node.IsLt(r.num, p.Power)) {
            // r.num < p.Power
            lhs = node.Env.StrManager.Drop(lhs, fwd);
            rhs = node.Env.StrManager.Drop(rhs, (uint)r.idx, fwd);
            var sub = p.Power.Sub(r.num);
            lhs = node.Env.StrManager.Concat(PowerToken.MkPower(p.Base, sub, node.Env), lhs, fwd);
            Log.WriteLine("Simplify: power-elim " + p);
            return true;
        }
        if (node.IsLe(p.Power, r.num) || node.IsLt(p.Power, r.num)) {
            // p.Power <= r.num
            lhs = node.Env.StrManager.Drop(lhs, fwd);
            rhs = node.Env.StrManager.Drop(rhs, (uint)r.idx, fwd);
            var sub = r.num.Sub(p.Power);
            rhs = node.Env.StrManager.Concat(PowerToken.MkPower(p.Base, sub, node.Env), rhs, fwd);
            Log.WriteLine("Simplify: power-elim " + p);
            return true;
        }
        return false;
    }

    bool SimplifyPowerUnwind(NielsenNode node, PowerToken p, bool fwd) {
        if (!node.IsLt(node.Env.ZeroInt, p.Power))
            return false;

        Log.WriteLine("Simplify: >0-unwinding power " + p);
        // lhs.Unwind(dir, node);
        lhs = node.Env.StrManager.Drop(lhs, fwd);
        var sub = p.Power.Sub(node.Env.OneInt);
        lhs = node.Env.StrManager.Concat(node.Env.StrManager.Concat(p.Base, PowerToken.MkPower(p.Base, sub, node.Env), fwd), lhs, fwd);
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
    protected static Str? SimplifyPowerSingle(LocalInfo info, PowerToken p) {
        // This can be locally violated e.g., if some integer constraint simplified to 1 <= 0 so IsLt(1, 0) evaluates to true
        // Debug.Assert(!p.Power.IsConst(out var dl) || !dl.IsNeg);
        if (p.Power.TryGetConst(out var dl) && dl.Sign < 0)
            // We could also just ignore it, but probably not worth making efforts simplifying it
            return null;

        if (p.Base is { Length: 1, First: PowerToken p2 }) {
            // (u^m)^n => u^{mn}
            Dictionary<NamedInt, PDD<BigInteger>> definitions = [];
            var ret = PowerToken.MkPower(p2.Base, 
                PDD<BigInteger>.MulByDefinitions(p.Power, p2.Power, definitions), info.Env);
            foreach (var def in definitions) {
                info.CurrentNode.AddConstraint(new IntEq(info.Env.IntPDDManager.MkPDD(def.Key), def.Value));
            }
            return ret;
        }

        // ""^n => ""
        if (p.Base.IsEmpty()) {
            Log.WriteLine("Simplify: Resolve empty-power " + p);
            return info.Env.EmptyStr;
        }
        // u^0 => ""
        if (info.CurrentNode.IsPowerElim(p.Power)) {
            Log.WriteLine("Simplify: Drop 0-power " + p);
            return info.Env.EmptyStr;
        }
        // u^1 => u
        if (info.CurrentNode.IsOne(p.Power)) {
            Log.WriteLine("Simplify: Resolve 1-power " + p);
            return p.Base;
        }

        // Don't unwind based on bounds!! (Not good for detecting similar powers!)
        // If at all only based on known powers!

        if (Options.ReasoningUnwindingBound > 1) {
            // Unwind based on options...
            var bounds = p.Power.GetBounds(info.CurrentNode);
            if (bounds.IsUnit) {
                Debug.Assert((BigInteger)bounds.Min > 1);
                Log.WriteLine("Simplify: Resolve " + bounds.Min + "-power " + p);
                return info.Env.StrManager.Repeat(p.Base, (uint)(BigInteger)bounds.Min);
            }
        }

        // simplify((u^m v)^n) => (simplify(u^m) v)^n
        // Actually all, but not sure we need to apply it to all sub powers
        // (practical problem: We can only remove first/last element)
        List<Str?> partialList = [];
        bool has = false;
        for (int i = 0; i < p.Base.Length; i++) {
            Str? r = p.Base[i] is PowerToken p3 ? SimplifyPowerSingle(info, p3) : null;
            has |= r is not null;
            partialList.Add(r);
        }
        if (has) {
            List<StrToken> r = new((int)p.Base.Length);
            for (int i = 0; i < partialList.Count; i++) {
                if (partialList[i] is { } t2)
                    r.AddRange(t2.GetEnumerator());
                else
                    r.Add(p.Base[i]);
            }
            Debug.Assert(partialList.Any(o => o is not null));
            return PowerToken.MkPower(info.Env.MkString(r), p.Power, info.Env);
        }

        var lcp = LcpCompressionFull(p.Base, info.Env);
        if (lcp is not null)
            return PowerToken.MkPower(lcp, p.Power, info.Env);
        return null;
    }

    static int lcpCnt;

    // We apply the following steps:
    // v'uu...uv'' => v' u^n v'' (only if singleCompress)
    // v' u^m u^n v'' => v' u^{m + n} v''
    // v' u^n u v'' => v' u^{n + 1} v''
    // v' u' (u'u'')^n u'' v' => v' (u'u'')^{n+1} v'
    // till fixed point
    public static Str? LcpCompressionFull(Str s, Environment env) {
        if (s.Length < 2)
            return null;
        // TODO: Cache this
#if DEBUG
        Str orig = s;
#endif
        bool changed = false;
        while (MergeSingle(s, env) is { } v) {
            s = v;
            changed = true;
        }
        Str? r = LcpCompression(s, env);

#if DEBUG
        Log.WriteLine($"lcp-full ({lcpCnt}): {orig} => {s}");
#endif

        if (r is not null)
            return r;
        return changed ? s : null;
    }

    // Everything from *Full but compressing non-power sequences into powers 
    // [Distinction, as introducing powers on top-level might not be beneficial]
    public static Str? LcpCompression(Str s, Environment env) {
        if (s.Length < 2)
            return null;

        // Apply each at least once and then until the first one fails
        lcpCnt++;
        Str orig = s;

        bool globalChanged = false;
        bool changed1 = true;
        bool changed2 = true;

        while (changed1 || changed2) {
            Str? v = MergePowersRight(s, env);
            if (v is not null) {
                s = v;
                changed1 = true;
                globalChanged = true;
            }
            else
                changed1 = false;
            if (!changed1 && !changed2)
                break;
            v = MergePowersLeft(s, env);
            if (v is not null) {
                s = v;
                changed2 = true;
                globalChanged = true;
            }
            else
                changed2 = false;
        }
        Log.WriteLine($"lcp-short ({lcpCnt}): {orig} => {s}");
        return !globalChanged ? null : s;
    }

    // v'u...uv'' => v' u^n v'' (first only and preferring minimal compression: baaaab => b a^4 b rather than b (aa)^2 b)
    // u is ground
    // Implementation: Sliding window
    [Pure]
    static Str? MergeSingle(Str s, Environment env) {
        if (s.Length < 2)
            return null;
        uint to = s.Length / 2;
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
                    List<StrToken> r = new((int)(s.Length - rep * i + 1));
                    for (int k = 0; k < j; k++) {
                        r.Add(s[k]);
                    }
                    List<StrToken> b = new(rep);
                    for (int k = 0; k < i; k++) {
                        b.Add(s[j + k]);
                    }
                    r.Add(new PowerToken(env.MkString(b), env.IntPDDManager.MkPDD(rep)));
                    for (int k = j + rep * i; k < s.Length; k++) {
                        r.Add(s[k]);
                    }
                    Debug.Assert(r.Count == s.Length - rep * i + 1);
                    return env.MkString(r);
                }
            }
        }
        return null;
    }

    // v' u^m u^n v'' => v' u^{m + n} v''
    // v' u^n u v'' => v' u^{n + 1} v''
    [MethodImpl(MethodImplOptions.AggressiveInlining), Pure]
    static Str? MergePowersRight(Str s, Environment env) =>
        MergePowers(s, env, true);

    // v' u'' (u'u'')^n v' => v' (u''u')^{n+1} u'' v'
    // We traverse the sequence backwards.
    // If we encounter (u'u'')^n we traverse u'u'' backwards and check how long it works after the power
    [MethodImpl(MethodImplOptions.AggressiveInlining), Pure]
    static Str? MergePowersLeft(Str s, Environment env) =>
        MergePowers(s, env, false);

    [Pure]
    static Str? MergePowers(Str s, Environment env, bool fwd) {
        List<StrToken> p = new((int)s.Length);
        PDD<BigInteger> sum = env.ZeroInt;
        Str b = env.EmptyStr;
        Debug.Assert(sum.IsZero);

        // v' u^n u v'' => v' u^{n + 1} v''
        // Count how often this works
        uint LookAhead(uint pos) {
            uint max = (s.Length - pos) / b.Length;
            uint cnt = 0;
            for (; cnt < max; cnt++) {
                for (uint j = 0; j < b.Length; j++) {
                    if (!b[fwd, j].Equals(s[fwd, pos + b.Length * cnt + j]))
                        return cnt;
                }
            }
            return cnt;
        }

        bool compressed = false;
        for (uint i = 0; i < s.Length; i++) {
            if (s[fwd, i] is not PowerToken pow) {
                if (!sum.IsZero) {
                    Debug.Assert(b.IsNonEmpty());
                    p.Add(new PowerToken(b, sum));
                }
                b = env.EmptyStr;
                sum = env.ZeroInt;
                p.Add(s[fwd, i]);
                continue;
            }
            if (!pow.Base.Equals(b)) {
                if (!sum.IsZero) {
                    Debug.Assert(b.IsNonEmpty());
                    p.Add(new PowerToken(b, sum));
                }
                b = pow.Base;
                sum = pow.Power;
                uint cnt = LookAhead(i + 1);
                i += b.Length * cnt;
                sum = sum.Add(cnt);
                compressed |= cnt > 0;
                continue;
            }
            compressed = true;
            sum = sum.Add(pow.Power);
        }
        if (!sum.IsZero) {
            Debug.Assert(b.IsNonEmpty());
            p.Add(new PowerToken(b, sum));
        }
        return compressed ? env.MkString(p, fwd) : null;
    }

    public override void CollectSymbols(NonTermSet nonTermSet, HashSet<CharToken> alphabet) {
        LHS.CollectSymbols(nonTermSet, alphabet);
        RHS.CollectSymbols(nonTermSet, alphabet);
    }

    public override bool Contains(NamedStrToken namedStrToken) =>
        LHS.ContainsVar(namedStrToken) || RHS.ContainsVar(namedStrToken);

    public int CompareTo(StrEqBase? other) {
        if (other is null)
            return 1;
        int cmp = LHS.CompareTo(other.LHS);
        return cmp != 0 ? cmp : RHS.CompareTo(other.RHS);
    }

}
