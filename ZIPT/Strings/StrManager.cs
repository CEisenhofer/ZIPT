using Microsoft.Z3;
using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.Net.Http.Headers;
using System.Numerics;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using ZIPT.Constraints;
using ZIPT.Constraints.ConstraintElement;
using ZIPT.IntUtils;
using ZIPT.Strings.Chunks;
using ZIPT.Strings.Tokens;

namespace ZIPT.Strings;

public sealed class StrManager {

    readonly Dictionary<(uint, uint), TupleStr> tupleChunks = [];
    readonly Dictionary<StrToken, SingletonStr> singleChunks = [];

    public EmptyStr EmptyStr { get; }

    uint nextChunkId;

    public StrManager() =>
        EmptyStr = new EmptyStr(nextChunkId++);

    [MethodImpl(MethodImplOptions.AggressiveInlining), Pure]
    public static StrToken GetIndex(Str str, uint idx, bool fwd) => 
        fwd ? GetIndexFwd(str, idx) : GetIndexBwd(str, idx);

    public static StrToken GetIndexFwd(Str str, uint idx) {
        Debug.Assert(idx < str.Length);
        while (idx > 0) {
            Debug.Assert(str is TupleStr);
            TupleStr ts = (TupleStr)str;
            if (idx < ts.Left.Length) {
                str = ts.Left;
            }
            else {
                idx -= ts.Left.Length;
                str = ts.Right;
            }
        }
        while (str is TupleStr ts) {
            str = ts.Left;
        }
        Debug.Assert(str is SingletonStr);
        return ((SingletonStr)str).StrToken;
    }

    public static StrToken GetIndexBwd(Str str, uint idx) {
        Debug.Assert(idx < str.Length);
        while (idx > 0) {
            Debug.Assert(str is TupleStr);
            TupleStr ts = (TupleStr)str;
            if (idx < ts.Right.Length) {
                str = ts.Right;
            }
            else {
                idx -= ts.Right.Length;
                str = ts.Left;
            }
        }
        while (str is TupleStr ts) {
            str = ts.Right;
        }
        Debug.Assert(str is SingletonStr);
        return ((SingletonStr)str).StrToken;
    }


    [MethodImpl(MethodImplOptions.AggressiveInlining), Pure]
    public Str Extract(Str str, uint cnt, bool fwd) => 
        fwd ? ExtractFwd(str, cnt) : ExtractBwd(str, cnt);

    public Str ExtractFwd(Str str, uint cnt) => 
        DropRight(str, str.Length - cnt);

    public Str ExtractBwd(Str str, uint cnt) =>
        DropLeft(str, str.Length - cnt);

    [MethodImpl(MethodImplOptions.AggressiveInlining), Pure]
    public Str Concat(StrToken left, StrToken right) =>
        Concat(Single(left), Single(right));

    [MethodImpl(MethodImplOptions.AggressiveInlining), Pure]
    public Str Concat(Str left, StrToken right) =>
        Concat(left, Single(right));

    [MethodImpl(MethodImplOptions.AggressiveInlining), Pure]
    public Str Concat(StrToken left, Str right) =>
        Concat(Single(left), right);

    [MethodImpl(MethodImplOptions.AggressiveInlining), Pure]
    public Str Concat(Str left, StrToken right, bool fwd) =>
        Concat(left, Single(right), fwd);


    [MethodImpl(MethodImplOptions.AggressiveInlining), Pure]
    public Str Concat(StrToken left, Str right, bool fwd) =>
        Concat(Single(left), right, fwd);

    [Pure]
    public Str Concat(Str left, Str right, bool fwd) =>
        fwd ? Concat(left, right) : Concat(right, left);

    [Pure]
    public Str Concat(Str left, Str right) {
        if (left is EmptyStr)
            return right;
        if (right is EmptyStr)
            return left;
        Debug.Assert(left.BalancedTrans);
        Debug.Assert(right.BalancedTrans);
        Debug.Assert(left is SingletonStr or TupleStr);
        Debug.Assert(right is SingletonStr or TupleStr);

        // TODO: just left/right; don't create the object
        Stack<(Str, bool)> toMerge = new((int)Math.Max(left.Level, right.Level));

        while (!TupleStr.IsBalanced(left, right)) {
            if (tupleChunks.TryGetValue((left.ChunkId, right.ChunkId), out var cached)) {
                Debug.Assert(cached.BalancedTrans);
                left = cached.Left;
                right = cached.Right;
                break;
            }
            if (left.Level < right.Level) {
                var sub = (TupleStr)right;
                if (sub.Left.Level <= sub.Right.Level) {
                    // left rotation
                    toMerge.Push((sub.Right, true));
                    right = sub.Left;
                }
                else {
                    // double left rotation
                    var res = CreateChunk(((TupleStr)sub.Left).Right, sub.Right);
                    toMerge.Push((res, true));
                    right = ((TupleStr)sub.Left).Left;
                }
            }
            else {
                var sub = (TupleStr)left;
                if (sub.Right.Level <= sub.Left.Level) {
                    toMerge.Push((sub.Left, false));
                    left = sub.Right;
                }
                else {
                    var res = CreateChunk(sub.Left, ((TupleStr)sub.Right).Left);
                    toMerge.Push((res, false));
                    left = ((TupleStr)sub.Right).Right;
                }
            }
        }

        Str ret = CreateChunk(left, right);
        while (toMerge.Count > 0) {
            var (rest, isLeft) = toMerge.Pop();
            if (isLeft) {
                ret = TupleStr.IsBalanced(ret, rest) 
                    ? CreateChunk(ret, rest) 
                    // This is a very rare case [double rotation was not enough]
                    : Concat(ret, rest);
                continue;
            }
            ret = TupleStr.IsBalanced(ret, rest)
                ? CreateChunk(rest, ret)
                : Concat(rest, ret);
        }

        Debug.Assert(ret.BalancedTrans);
        Debug.Assert(!ret.IsTemp);
        return ret;
    }

    [Pure]
    Str CreateChunk(Str left, Str right) {
        if (left is EmptyStr)
            return right;
        if (right is EmptyStr)
            return left;
        if (tupleChunks.TryGetValue((left.ChunkId, right.ChunkId), out var chunk))
            return chunk;
        Debug.Assert(left.BalancedTrans);
        Debug.Assert(right.BalancedTrans);
        chunk = new TupleStr(nextChunkId++, left, right);
        Debug.Assert(chunk.Balanced);
        tupleChunks.Add((left.ChunkId, right.ChunkId), chunk);
        return chunk;
    }

    [Pure]
    public SingletonStr Single(StrToken token) {
        if (singleChunks.TryGetValue(token, out var chunk))
            return chunk;
        singleChunks.Add(token, chunk = new SingletonStr(nextChunkId++, token));
        return chunk;
    }

    [Pure]
    public Str Drop(Str s, uint cnt, bool fwd) => 
        fwd ? DropLeft(s, cnt) : DropRight(s, cnt);

    [Pure]
    public Str Drop(Str s, bool fwd) =>
        Drop(s, 1, fwd);

    [Pure]
    public Str DropLeft(Str str, uint cnt = 1) {
        Debug.Assert(cnt <= str.Length);
        if (cnt == 0)
            return str;
        if (str.Length == cnt)
            return EmptyStr;
        uint cntOrig = cnt;
        Debug.Assert(str is TupleStr);
        if (((TupleStr)str).DropLeftCache.TryGetValue(cnt, out var val))
            return val;

        var current = str;
        List<Str> toConcat = new((int)current.Level);

        while (cnt > 0) {
            TupleStr tupleStr = (TupleStr)current;
            if (cnt < tupleStr.Left.Length) {
                toConcat.Add(tupleStr.Right);
                current = tupleStr.Left;
            }
            else {
                cnt -= tupleStr.Left.Length;
                current = tupleStr.Right;
            }
        }

        Str res = current;
        for (int i = toConcat.Count; i > 0; i--) {
            res = Concat(res, toConcat[i - 1]);
        }
        ((TupleStr)str).DropLeftCache.Add(cntOrig, res);
        return res;
    }

    [Pure]
    public Str DropRight(Str str, uint cnt = 1) {
        Debug.Assert(cnt <= str.Length);
        if (cnt == 0)
            return str;
        if (str.Length == cnt)
            return EmptyStr;
        uint cntOrig = cnt;
        Debug.Assert(str is TupleStr);
        if (((TupleStr)str).DropRightCache.TryGetValue(cnt, out var val))
            return val;

        var current = str;
        List<Str> toConcat = new((int)current.Level);

        while (cnt > 0) {
            TupleStr tupleStr = (TupleStr)current;
            if (cnt < tupleStr.Right.Length) {
                toConcat.Add(tupleStr.Left);
                current = tupleStr.Right;
            }
            else {
                cnt -= tupleStr.Right.Length;
                current = tupleStr.Left;
            }
        }

        Str res = current;
        for (int i = toConcat.Count; i > 0; i--) {
            res = Concat(toConcat[i - 1], res);
        }
        ((TupleStr)str).DropRightCache.Add(cntOrig, res);
        return res;
    }

    [Pure]
    public Str Subst(Str str, Interpretation itp) {
        if (str.IsEmpty())
            return str;
        if (str is SingletonStr s) {
            if (s.StrToken is NamedStrToken v && itp.Substitution.TryGetValue(v, out Str? newStr))
                return newStr;
            if (s.StrToken is PowerToken p) {
                var newBase = Subst(p.Base, itp);
                var newPower = PDD<BigInteger>.Substitute(p.Power, itp);
                if (!ReferenceEquals(newBase, p.Base) || !ReferenceEquals(newPower, p.Power))
                    return Single(new PowerToken(newBase, newPower));
            }
            return str;
        }

        Debug.Assert(str is TupleStr);
        TupleStr tc = (TupleStr)str;
        // TODO: Make iterative
        var left = Subst(tc.Left, itp);
        var right = Subst(tc.Right, itp);
        var res = Concat(left, right);
        Debug.Assert(res.BalancedTrans);
        return res;
    }

    [Pure]
    public Str Subst(Str str, Subst subst) =>
        Subst(str, subst.Var, subst.Str);

    [Pure]
    public Str Subst(Str str, NamedStrToken v, Str repl) {
        if (!str.ContainsVar(v))
            return str;
        if (str is SingletonStr)
            return repl;

        Debug.Assert(str is TupleStr);
        TupleStr tc = (TupleStr)str;
        if (tc.SubstCache.TryGetValue((v, repl), out var res))
            return res;
        // TODO: Make iterative
        var left = Subst(tc.Left, v, repl);
        var right = Subst(tc.Right, v, repl);
        res = Concat(left, right);
        Debug.Assert(!tc.SubstCache.ContainsKey((v, repl)));
        tc.SubstCache.Add((v, repl), res);
        Debug.Assert(res.BalancedTrans);
        return res;
    }

    public static bool IsNullable(NielsenNode node, Str s) {
        Stack<Str> todo = new();
        while (true) {
            while (s is TupleStr lts) {
                todo.Push(lts.Right);
                s = lts.Left;
            }
            Debug.Assert(s is SingletonStr);
            if (!((SingletonStr)s).StrToken.IsNullable(node))
                return false;
            if (todo.Count == 0)
                return true;
            Debug.Assert(todo.Count > 0);
            s = todo.Pop();
        }
    }

    // Proper prefixes
    public static List<PrefixDecomposition> GetPrefixes(NielsenNode node, Str s, bool fwd) {
        // P(u_1...u_n) := P(u_1) | u_1 P(u_2) | ... | u_1...u_{n-1} P(u_n)
        List<PrefixDecomposition> ret = [];
        Str prefix = node.Env.EmptyStr;
        for (int i = 0; i < s.Length; i++) {
            var current = s[fwd, i].GetPrefixes(node, fwd);
            for (int j = 0; j < current.Count; j++) {
                if (fwd)
                    current[j].Str = node.Env.StrManager.Concat(current[j].Str, prefix);
                else
                    current[j].Str = node.Env.StrManager.Concat(prefix, current[j].Str);
            }
            ret.AddRange(current);
            prefix = node.Env.StrManager.Concat(prefix, s[fwd, i]);
        }
        return ret;
    }

    [Pure]
    public Str FromList(List<StrToken> tokens, bool fwd = true) =>
        FromList(CollectionsMarshal.AsSpan(tokens), fwd);

    [Pure]
    public Str FromList(StrToken[] tokens, bool fwd = true) => 
        FromList(tokens.AsSpan(), fwd);

    [Pure]
    public Str FromList(ReadOnlySpan<StrToken> tokens, bool fwd = true) =>
        fwd ? FromListFwd(tokens) : FromListBwd(tokens);

    [Pure]
    public Str FromListFwd(ReadOnlySpan<StrToken> tokens) =>
        tokens.Length switch {
            0 => EmptyStr,
            1 => Single(tokens[0]),
            2 => CreateChunk(Single(tokens[0]), Single(tokens[1])),
            _ => Concat(FromListFwd(tokens[..(tokens.Length / 2)]),
                FromListFwd(tokens[(tokens.Length / 2)..])),
        };

    [Pure]
    public Str FromListBwd(ReadOnlySpan<StrToken> tokens) =>
        tokens.Length switch {
            0 => EmptyStr,
            1 => Single(tokens[0]),
            2 => CreateChunk(Single(tokens[1]), Single(tokens[0])),
            _ => Concat(FromListBwd(tokens[(tokens.Length / 2)..]),
                FromListBwd(tokens[..(tokens.Length / 2)])),
        };


    public Str Repeat(Str s, uint rep) {
        Str core = s;
        Str rest = EmptyStr;
        while (rep > 0) {
            Str concat = Concat(core, core);
            if (rep % 2 == 1)
                rest = Concat(core, rest);
            core = concat;
            rep /= 2;
        }
        return rest;
    }

    [Pure]
    public static IEnumerable<StrToken> GetEnumerator(Str s, uint skip) {
        if (skip == s.Length)
            yield break;
        Debug.Assert(skip <= s.Length);
        Stack<Str> todo = [];
        while (skip > 0) {
            Debug.Assert(s is TupleStr);
            TupleStr lts = (TupleStr)s;
            if (skip < lts.Left.Length) {
                todo.Push(lts.Right);
                s = lts.Left;
            }
            else {
                skip -= lts.Left.Length;
                s = lts.Right;
            }
        }
        while (true) {
            while (s is TupleStr lts) {
                todo.Push(lts.Right);
                s = lts.Left;
            }
            Debug.Assert(s is SingletonStr);
            yield return ((SingletonStr)s).StrToken;
            if (todo.Count == 0)
                yield break;
            Debug.Assert(todo.Count > 0);
            s = todo.Pop();
        }
    }

    [Pure]
    public static IEnumerable<StrToken> GetRevEnumerator(Str s) {
        Stack<Str> todo = [];
        while (true) {
            while (s is TupleStr lts) {
                todo.Push(lts.Left);
                s = lts.Right;
            }
            Debug.Assert(s is SingletonStr);
            yield return ((SingletonStr)s).StrToken;
            if (todo.Count == 0)
                yield break;
            Debug.Assert(todo.Count > 0);
            s = todo.Pop();
        }
    }

    [Pure]
    public static Expr ToExpr(Str s, NielsenGraph graph) {
        if (s.IsEmpty())
            return graph.Env.Epsilon;
        using var e = GetRevEnumerator(s).GetEnumerator();
        if (!e.MoveNext()) {
            Debug.Assert(false);
            return graph.Env.Epsilon;
        }
        Expr expr = e.Current.ToExpr(graph);
        while (e.MoveNext()) {
            expr = graph.Env.MkConcat(e.Current.ToExpr(graph), expr);
        }
        return expr;
    }
}