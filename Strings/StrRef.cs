using System.Collections;
using System.Diagnostics;
using System.Diagnostics.CodeAnalysis;
using Microsoft.Z3;
using static System.Runtime.InteropServices.JavaScript.JSType;
using StringBreaker.Constraints.ConstraintElement;
using StringBreaker.Constraints;
using StringBreaker.IntUtils;
using StringBreaker.MiscUtils;
using StringBreaker.Strings.Tokens;
using System.Diagnostics.Metrics;

namespace StringBreaker.Strings;

public class StrRef {

    Str beginStr;
    Str endStr;
    int beginIdx;
    int endIdx;

    public Str BeginStr => beginStr;
    public Str EndStr => endStr;
    public int BeginIdx => beginIdx;
    public int EndIdx => endIdx;


    StrRef? backBeginStr;
    int backBeginIdx;
    StrRef? backEndStr;
    int backEndIdx;

    public StrRef(
        Str beginStr, int beginIdx,
        Str endStr, int endIdx,
        StrRef? backBeginStr, int backBeginIdx,
        StrRef? backEndStr, int backEndIdx) {

        this.beginStr = beginStr;
        this.endStr = endStr;
        this.beginIdx = beginIdx;
        this.endIdx = endIdx;
        this.backBeginStr = backBeginStr;
        this.backBeginIdx = backBeginIdx;
        this.backEndStr = backEndStr;
        this.backEndIdx = backEndIdx;
        Debug.Assert(beginIdx >= 0);
        Debug.Assert(endIdx >= 0);
        Debug.Assert(backBeginIdx >= 0);
        Debug.Assert(backEndIdx >= 0);
        Debug.Assert(beginIdx <= beginStr.Count);
        Debug.Assert(endIdx <= endStr.Count);
    }

    public StrRef(Str beginStr, int beginIdx, Str endStr, int endIdx) :
        this(beginStr, beginIdx, endStr, endIdx, null, 0, null, 0) { }

    public StrRef(StrRef from, StrRef to, bool dir) :
        this(dir ? from.beginStr : to.endStr,
            dir ? from.beginIdx : to.endIdx,
            dir ? to.beginStr : from.endStr,
            dir ? to.beginIdx : from.endIdx) { }

    public StrRef(Str s) : this(s, 0, s, s.Count - 1, null, 0, null, 0) { }

    public bool IsInLeft(NielsenContext ctx) {
        var c = Clone();
        c.MoveInLeft(ctx);
        return c.Equals(this);
    }

    public bool IsInRight(NielsenContext ctx) {
        var c = Clone();
        c.MoveInRight(ctx);
        return c.Equals(this);
    }

    public bool IsEpsilon(NielsenContext ctx) {
        var clone = Clone();
        clone.MoveInLeft(ctx);
        clone.MoveInRight(ctx);
        return 
            clone.beginIdx == clone.endIdx &&
            clone.beginStr.Equals(clone.endStr);
    }

    public void MoveInLeft(NielsenContext ctx) {
        while (true) {
            if (beginIdx == endIdx && beginStr.Equals(endStr))
                return;
            if (beginIdx >= beginStr.Count) {
                Debug.Assert(beginIdx == beginStr.Count);
                Debug.Assert(backBeginStr is not null);
                beginStr = backBeginStr.beginStr;
                beginIdx = backBeginIdx;
                backBeginIdx = backBeginStr.backBeginIdx + 1;
                backBeginStr = backBeginStr.backBeginStr;
                continue;
            }
            var r = beginStr[beginIdx].ResolveTo(ctx);
            if (r is null)
                return;
        }
    }

    public void MoveInRight(NielsenContext ctx) {
        while (true) {
            if (endIdx == beginIdx && endStr.Equals(beginStr))
                return;
            if (endIdx < 0) {
                Debug.Assert(endIdx == -1);
                Debug.Assert(backEndStr is not null);
                endStr = backEndStr.endStr;
                endIdx = backEndIdx;
                backEndIdx = backEndStr.backEndIdx - 1;
                backEndStr = backEndStr.backEndStr;
                continue;
            }
            var r = endStr[endIdx].ResolveTo(ctx);
            if (r is null)
                return;
        }
    }

    public bool IsUnit(NielsenContext ctx, [NotNullWhen(true)] out StrTokenRef? unit) {
        unit = null;
        var c = Clone();
        unit = c.PeekFirst(ctx);
        if (unit is null)
            return false;
        c.SkipFirst(ctx);
        return c.IsEpsilon(ctx);
    }

    public IEnumerable<StrTokenRef> Enumerate(NielsenContext ctx) {
        var clone = Clone();
        while (!clone.IsEpsilon(ctx)) {
            yield return clone.PeekFirst(ctx)!;
            clone.SkipFirst(ctx);
        }
    }

    public IEnumerable<StrTokenRef> EnumerateBack(NielsenContext ctx) {
        var clone = Clone();
        while (!clone.IsEpsilon(ctx)) {
            yield return clone.PeekLast(ctx)!;
            clone.SkipLast(ctx);
        }
    }

    // Don't use with high cnt - the data structure is not meant to be random access!!
    public StrTokenRef? Peek(NielsenContext ctx, int cnt, bool dir) =>
        dir ? PeekFirst(ctx, cnt) : PeekLast(ctx, cnt);

    public StrTokenRef? Peek(NielsenContext ctx, bool dir) =>
        dir ? PeekFirst(ctx) : PeekLast(ctx);

    public StrTokenRef Peek2(NielsenContext ctx, bool dir) {
        var r = Peek(ctx, dir);
        if (r is null)
            throw new InvalidOperationException();
        return r;
    }

    public StrTokenRef? PeekFirst(NielsenContext ctx) {
        if (IsEpsilon(ctx))
            return null;
        Debug.Assert(IsInLeft(ctx));
        Debug.Assert(beginIdx >= 0);
        Debug.Assert(beginIdx < beginStr.Count);
        return beginStr[beginIdx];
    }

    public StrTokenRef? PeekLast(NielsenContext ctx) {
        if (IsEpsilon(ctx))
            return null;
        Debug.Assert(IsInRight(ctx));
        Debug.Assert(endIdx >= 0);
        Debug.Assert(endIdx < endStr.Count);
        return endStr[endIdx];
    }

    public StrTokenRef? PeekFirst(NielsenContext ctx, int cnt) {
        for (int i = 0; i < cnt; i++) {
            if (IsEpsilon(ctx))
                return null;
            Debug.Assert(IsInLeft(ctx));
            Debug.Assert(beginIdx >= 0);
            Debug.Assert(beginIdx < beginStr.Count);
        }
        return beginStr[beginIdx];
    }

    public StrTokenRef? PeekLast(NielsenContext ctx, int cnt) {
        for (int i = 0; i < cnt; i++) {
            if (IsEpsilon(ctx))
                return null;
            Debug.Assert(IsInRight(ctx));
            Debug.Assert(endIdx >= 0);
            Debug.Assert(endIdx < endStr.Count);
        }
        return endStr[endIdx];
    }

    public StrTokenRef SkipFirst(NielsenContext ctx) {
        Debug.Assert(IsInLeft(ctx));
        var res = PeekFirst(ctx);
        Debug.Assert(res is not null);
        beginIdx++;
        return res;
    }

    public StrTokenRef SkipLast(NielsenContext ctx) {
        Debug.Assert(IsInRight(ctx));
        var res = PeekLast(ctx);
        Debug.Assert(res is not null);
        endIdx--;
        return res;
    }

    public StrTokenRef Skip(NielsenContext ctx, bool dir) => 
        dir ? SkipFirst(ctx) : SkipLast(ctx);

    public bool IsNullable(NielsenContext ctx) => 
        Enumerate(ctx).All(o => o.Token.IsNullable(ctx));

    // Proper prefixes
    public List<(Str str, List<IntConstraint> sideConstraints, Subst? varDecomp)> GetPrefixes(bool dir) {
        // P(u_1...u_n) := P(u_1) | u_1 P(u_2) | ... | u_1...u_{n-1} P(u_n)
        List<(Str str, List<IntConstraint> sideConstraints, Subst? varDecomp)> ret = [];
        Str prefix = [];
        for (int i = 0; i < Count; i++) {
            var current = Peek(dir, i).GetPrefixes(dir);
            for (int j = 0; j < current.Count; j++) {
                current[j].str.AddRange(prefix, dir);
            }
            ret.AddRange(current);
            prefix.Add(Peek(dir, i), !dir);
        }
        return ret;
    }

    public Expr ToExpr(NielsenContext ctx) {
        using var it = EnumerateBack(ctx).GetEnumerator();
        if (!it.MoveNext())
            return ctx.Cache.Epsilon;
        Expr last = it.Current.ToExpr(ctx);
        while (it.MoveNext()) {
            last = ctx.Cache.MkConcat(it.Current.ToExpr(ctx), last);
        }
        return last;
    }

    public void CollectSymbols(NielsenContext ctx,
        HashSet<NamedStrToken> vars, HashSet<SymCharToken> sChars, 
        HashSet<IntVar> iVars, HashSet<CharToken> alphabet) {

        foreach (var token in Enumerate(ctx)) {
            StrRef? r = token.ResolveTo(ctx);
            if (r is not null) {
                r.CollectSymbols(ctx, vars, sChars, iVars, alphabet);
                continue;
            }
            switch (token.Token) {
                case StrVarToken v:
                    vars.Add(v);
                    break;
                case CharToken c:
                    alphabet.Add(c);
                    break;
                case SymCharToken s:
                    sChars.Add(s);
                    break;
                case PowerToken p:
                    p.Base.CollectSymbols(ctx, vars, sChars, iVars, alphabet);
                    p.Power.CollectSymbols(vars, sChars, iVars, alphabet);
                    break;
                default:
                    throw new NotSupportedException();
            }
        }
    }

    public override bool Equals(object? obj) =>
        obj is StrRef other && Equals(other);

    public bool Equals(StrRef other) =>
        beginIdx == other.beginIdx && endIdx == other.endIdx &&
        beginStr.Equals(other.beginStr) && endStr.Equals(other.endStr);

    public override int GetHashCode() =>
        HashCode.Combine(
            beginStr,
            beginIdx,
            endStr,
            endIdx
        );

    public override string ToString() => 
        $"{beginStr}[{beginIdx}] => {endStr}[{endIdx}]";

    public string ToString(NielsenContext ctx) {
        string s = string.Concat(Enumerate(ctx).Select(o =>
        {
            var r = o.ResolveTo(ctx);
            return r is not null ? r.ToString(ctx) : o.Token.ToString();
        }));
        return s.Length == 0 ? "ε" : s;
    }

    public StrRef Clone() => new(
        beginStr, beginIdx,
        endStr, endIdx,
        backBeginStr, backBeginIdx,
        backEndStr, backEndIdx);

    public int CompareTo(StrRef? other) {
        if (ReferenceEquals(this, other))
            return 0;
        if (other is null)
            return 1;
        int cmp = beginStr.CompareTo(other.beginStr);
        if (cmp != 0)
            return cmp;
        cmp = beginIdx.CompareTo(other.beginIdx);
        if (cmp != 0)
            return cmp;
        cmp = endStr.CompareTo(other.endStr);
        if (cmp != 0)
            return cmp;
        return endIdx.CompareTo(other.endIdx);
    }

}