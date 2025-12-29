using Microsoft.Z3;
using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.Numerics;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using ZIPT.Constraints;
using ZIPT.IntUtils;
using ZIPT.MiscUtils;
using ZIPT.Strings.Chunks;
using ZIPT.Strings.Tokens;
using ZIPT.Strings.Tokens.RegexTokens;

namespace ZIPT.Strings;

public sealed class StrManager {

    readonly Dictionary<(uint, uint), TupleStr> tupleChunks = [];
    readonly Dictionary<StrToken, SingletonStr> singleChunks = [];
    readonly Dictionary<Str, Str> representative = []; // multiple strings might have different binary tree structures

    public EmptyStr EmptyStr { get; }
    public SingletonStr FailStr { get; }
    public SingletonStr AllStr { get; }
    public SingletonStr AllChar { get; }

    uint nextChunkId;

    public StrManager() {
        EmptyStr = new EmptyStr(nextChunkId++);
        FailStr = Single(new FailToken());
        AllChar = Single(new SetToken(CharacterSet.Full));
        AllStr = (SingletonStr)MkStar(AllChar);
    }

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
    public Str Concat(Str s1, StrToken right) =>
        Concat(s1, Single(right));

    [MethodImpl(MethodImplOptions.AggressiveInlining), Pure]
    public Str Concat(StrToken left, Str s2) =>
        Concat(Single(left), s2);

    [MethodImpl(MethodImplOptions.AggressiveInlining), Pure]
    public Str Concat(Str s1, StrToken right, bool fwd) =>
        Concat(s1, Single(right), fwd);


    [MethodImpl(MethodImplOptions.AggressiveInlining), Pure]
    public Str Concat(StrToken left, Str s2, bool fwd) =>
        Concat(Single(left), s2, fwd);

    [Pure]
    public Str Concat(Str s1, Str s2, bool fwd) =>
        fwd ? Concat(s1, s2) : Concat(s2, s1);

    [Pure]
    public Str Concat(Str s1, Str s2) {
        while (true) {
            if (s1 is EmptyStr)
                return s2;
            if (s2 is EmptyStr)
                return s1;
            if (s1.IsFail)
                return FailStr;
            if (s2.IsFail)
                return FailStr;
            var last = s1.Last;
            var first = s2.First;
            // TODO: We need some more rules here
            // TODO: if s1 ends with r* and s2 starts with r*, merge
            if (last.IsFull && first.Nullable) {
                // u.* + vw = u.*w    if v nullable
                s2 = DropLeft(s2);
                continue;
            }
            if (last.Nullable && first.IsFull) {
                // uv + .*w = u.*w    if v nullable
                s1 = DropRight(s1);
                continue;
            }
            if (last is KleeneToken k1 && first is KleeneToken k2 && k1.Base.Equals(k2.Base)) {
                // uv* + v*w = uv*w
                s1 = DropRight(s1);
                continue;
            }
            if (last is LoopToken l1 && first is LoopToken l2 && l1.Base.Equals(l2.Base)) {
                // uv{l1,h1} + v{l2,h2}w = uv{l1+l2,h1+h2}w
                Str newLoop = MkLoop(l1.Base, l1.Min + l2.Min, l1.Max + l2.Max);
                s1 = DropRight(s1);
                s2 = DropLeft(s2);
                s2 = Concat(newLoop, s2);
                continue;
            }
            if (last is LoopToken l3 && StartsWith(s2, l3.Base)) {
                // uv{l,h} + vw = uv{l+1,h+1}w
                s1 = DropRight(s1);
                s2 = DropLeft(s2, l3.Base.Length);
                Str newLoop = MkLoop(l3.Base, l3.Min + 1, l3.Max + 1);
                s2 = Concat(newLoop, s2);
                continue;
            }
            if (first is LoopToken l4 && EndsWith(s1, l4.Base)) {
                // uv + v{l,h}w = uv{l+1,h+1}w
                s1 = DropRight(s1, l4.Base.Length);
                s2 = DropLeft(s2);
                Str newLoop = MkLoop(l4.Base, l4.Min + 1, l4.Max + 1);
                s1 = Concat(s1, newLoop);
                continue;
            }
            break;
        }
        Debug.Assert(s1.BalancedTrans);
        Debug.Assert(s2.BalancedTrans);
        Debug.Assert(s1 is SingletonStr or TupleStr);
        Debug.Assert(s2 is SingletonStr or TupleStr);

        // TODO: just left/right; don't create the object
        Stack<(Str, bool)> toMerge = new((int)Math.Max(s1.Level, s2.Level));

        while (!TupleStr.IsBalanced(s1, s2)) {
            if (tupleChunks.TryGetValue((s1.ChunkId, s2.ChunkId), out var cached)) {
                Debug.Assert(cached.BalancedTrans);
                s1 = cached.Left;
                s2 = cached.Right;
                break;
            }
            if (s1.Level < s2.Level) {
                var sub = (TupleStr)s2;
                if (sub.Left.Level <= sub.Right.Level) {
                    // left rotation
                    toMerge.Push((sub.Right, true));
                    s2 = sub.Left;
                }
                else {
                    // double left rotation
                    var res = CreateChunk(((TupleStr)sub.Left).Right, sub.Right);
                    toMerge.Push((res, true));
                    s2 = ((TupleStr)sub.Left).Left;
                }
            }
            else {
                var sub = (TupleStr)s1;
                if (sub.Right.Level <= sub.Left.Level) {
                    toMerge.Push((sub.Left, false));
                    s1 = sub.Right;
                }
                else {
                    var res = CreateChunk(sub.Left, ((TupleStr)sub.Right).Left);
                    toMerge.Push((res, false));
                    s1 = ((TupleStr)sub.Right).Right;
                }
            }
        }

        Str ret = CreateChunk(s1, s2);
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
        Stats.NewStringTuple++;
        if (tupleChunks.TryGetValue((left.ChunkId, right.ChunkId), out var chunk)) {
            Stats.CachedStringTuple++;
            return chunk;
        }
        Debug.Assert(left.BalancedTrans);
        Debug.Assert(right.BalancedTrans);
        chunk = new TupleStr(nextChunkId++, left, right);

        if (chunk.IsDegenerated) {
            TupleStr balanced = (TupleStr)FromUnbalancedStr(chunk);
            tupleChunks.Add((left.ChunkId, right.ChunkId), balanced);
            Stats.DegeneratedCnt++;
            return balanced;
        }
        tupleChunks.Add((left.ChunkId, right.ChunkId), chunk);
        Debug.Assert(chunk.Balanced);
        if (representative.TryGetValue(chunk, out var rep)) {
            int cmp = chunk.DegenerationLevel.CompareTo(rep.DegenerationLevel);
            if (cmp < 0) {
                rep.Normalised = chunk;
                representative[rep] = chunk;
            }
            else
                chunk.Normalised = rep;
            return cmp > 0 ? rep : chunk;
        }
        representative.TryAdd(chunk, chunk);
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
        TupleStr tuple = (TupleStr)str;
        Stats.StringLeftDropping++;
        if (tuple.DropLeftCache is not null && tuple.DropLeftCache.TryGetValue(cnt, out var val)) {
            Stats.CachedStringLeftDropping++;
            return val;
        }

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
        tuple.DropLeftCache ??= new Dictionary<uint, Str>();
        tuple.DropLeftCache.Add(cntOrig, res);
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
        TupleStr tuple = (TupleStr)str;
        Stats.StringRightDropping++;
        if (tuple.DropRightCache is not null && tuple.DropRightCache.TryGetValue(cnt, out var val)) {
            Stats.CachedStringRightDropping++;
            return val;
        }

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
        tuple.DropRightCache ??= new Dictionary<uint, Str>();
        tuple.DropRightCache.Add(cntOrig, res);
        return res;
    }

    [Pure]
    public Str SubStr(Str str, int from, int len) =>
        SubStr(str, (uint)from, (uint)len);

    [Pure]
    public Str SubStr(Str str, uint from, uint len) {
        Debug.Assert(from + len <= str.Length);
        Str s = DropLeft(str, from);
        s = DropRight(s, s.Length - len);
        return s;
    }

    [Pure]
    public Str Subst(Str str, Interpretation itp) {
        if (str.IsEmpty())
            return str;
        Stats.StringSubstitution++;
        if (str is SingletonStr s) {
            if (s.StrToken is NamedStrToken v && itp.Substitution.TryGetValue(v, out Subst subst))
                return subst.Str;
            if (s.StrToken is SymCharToken c && itp.CharSubstitution.TryGetValue(c, out CharSubst charSubst))
                return itp.Env.MkString(charSubst.Val);
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
        if (str.Ground)
            return str;
        if (!str.ContainsVar(v))
            return str;
        if (str is SingletonStr)
            return repl;

        Debug.Assert(str is TupleStr);
        TupleStr tc = (TupleStr)str;
        Stats.StringSubstitution++;
        if (tc.SubstCache is not null && tc.SubstCache.TryGetValue((v, repl), out var res)) {
            Stats.CachedStringSubstitution++;
            return res;
        }
        // TODO: Make iterative
        var left = Subst(tc.Left, v, repl);
        var right = Subst(tc.Right, v, repl);
        res = Concat(left, right);
        Debug.Assert(tc.SubstCache is null || !tc.SubstCache.ContainsKey((v, repl)));
        tc.SubstCache ??= new Dictionary<(NamedStrToken, Str), Str>();
        tc.SubstCache.Add((v, repl), res);
        Debug.Assert(res.BalancedTrans);
        return res;
    }

    [Pure]
    public Str Subst(Environment env, Str str, CharSubst subst) =>
        Subst(env, str, subst.Var, subst.Val);

    [Pure]
    public Str Subst(Environment env, Str str, SymCharToken v, UnitToken repl) {
        if (!str.ContainsSChar(v))
            return str;
        if (str is SingletonStr)
            return env.MkString(repl);

        Debug.Assert(str is TupleStr);
        TupleStr tc = (TupleStr)str;
        Stats.StringSubstitution++;
        if (tc.SubstCharCache is not null && tc.SubstCharCache.TryGetValue((v, repl), out var res)) {
            Stats.CachedStringSubstitution++;
            return res;
        }
        // TODO: Make iterative
        var left = Subst(env, tc.Left, v, repl);
        var right = Subst(env, tc.Right, v, repl);
        res = Concat(left, right);
        Debug.Assert(tc.SubstCharCache is null || !tc.SubstCharCache.ContainsKey((v, repl)));
        tc.SubstCharCache ??= new Dictionary<(SymCharToken, UnitToken), Str>();
        tc.SubstCharCache.Add((v, repl), res);
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
            if (!((SingletonStr)s).StrToken.Nullable)
                return false;
            if (todo.Count == 0)
                return true;
            Debug.Assert(todo.Count > 0);
            s = todo.Pop();
        }
    }

    // Proper prefixes
    public static List<StrDecomposition> GetDecompose(NielsenNode node, Str s, bool fwd) {
        // P(u_1...u_n) := P(u_1) | u_1 P(u_2) | ... | u_1...u_{n-1} P(u_n)
        // TODO: Cache this
        List<StrDecomposition> ret = [];
        Str prefix = node.Env.EmptyStr;
        Str postfix = s;
        for (int i = 0; i < s.Length; i++) {
            var current = s[fwd, i].GetDecomposition(node, fwd);
            postfix = node.Env.StrManager.Drop(postfix, fwd);
            for (int j = 0; j < current.Count; j++) {
                current[j].Prefix = node.Env.StrManager.Concat(prefix, current[j].Prefix, fwd);
            }
            for (int j = 0; j < current.Count; j++) {
                current[j].Postfix = node.Env.StrManager.Concat(current[j].Postfix, postfix, fwd);
            }
            ret.AddRange(current);
            prefix = node.Env.StrManager.Concat(prefix, s[fwd, i], fwd);
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

    [Pure]
    public Str FromUnbalancedStr(Str s) {
        Debug.Assert(s.IsDegenerated);
        Debug.Assert(s is not Chunks.EmptyStr && s is not SingletonStr);
        var list = s.ToArray();
        Debug.Assert(list.Length == (int)s.Length);
        return FromList(list);
    }

    [Pure]
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
    public Str MkComplement(Str s) {
        if (s.Length == 0)
            return Concat(AllChar, AllStr);
        if (s is { Length: 1, First: NotToken n })
            return n.Base;
        if (s is { Length: 1, IsFull: true })
            return FailStr;
        if (s is { Length: 1, IsFail: true })
            return AllStr;
        // these are WRONG:
        // if (s is { Length: 1, First: CharToken c })
        //     return Single(new SetToken(new CharacterSet(new CharacterRange(c.Value)).Complement()));
        // if (s is { Length: 1, First: SetToken set })
        //     return Single(new SetToken(set.Set.Complement()));
        return Single(new NotToken(s));
    }

    [Pure]
    public Str MkUnion(List<Str> tokens) {
        var subTokens = new List<Str>(tokens.Count);
        // Merge nested unions
        foreach (var t in tokens) {
            if (t is SingletonStr { StrToken: UnionToken u })
                subTokens.AddRange(u.Cases);
            else
                subTokens.Add(t);
        }
        tokens = subTokens;
        tokens.Sort();
        int copyIdx = 0;
        CharacterSet constSet = new();
        for (int i = 0; i < tokens.Count; i++) {
            if (copyIdx > 0 && tokens[i].Equals(tokens[copyIdx - 1]))
                continue;
            if (tokens[i].IsFail)
                continue;
            if (tokens[i].IsFull)
                return AllStr;
            // merge character sets
            if (tokens[i] is SingletonStr { StrToken: CharToken c })
                constSet.Add(c.Value);
            else if (tokens[i] is SingletonStr { StrToken: SetToken st })
                constSet.Add(st.Set);
            else {
                if (copyIdx > 0) {
                    // TODO: The same for intersection
                    if (tokens[copyIdx - 1] is { Length: 1, First: LoopToken lt1 } &&
                        tokens[i] is { Length: 1, First: LoopToken lt2 } && lt1.Base.Equals(lt2.Base)) {
                        // (...|b{l,h}|b{l',h'}|...) with l <= l' and h >= h'  ==> (...|b{l,h}|...)
                        if (lt1.Min <= lt2.Min && lt1.Max >= lt2.Max)
                            continue;
                        if (lt1.Min >= lt2.Min && lt1.Max <= lt2.Max) {
                            (tokens[copyIdx - 1], tokens[i]) = (tokens[i], tokens[copyIdx - 1]);
                            continue;
                        }
                    }
                    else {
                        // TODO: CommonSuffix as well?
                        uint len = CommonPrefix(tokens[copyIdx - 1], tokens[i]);
                        if (len > 0) {
                            Str s1 = tokens[copyIdx - 1];
                            Str s2 = tokens[i];
                            // (...|uv|uv'|...)  ==> (...|(u(v|v'))|...)
                            // TODO:
                            // to make this work well we need to change ordering that puts regexes with same prefix near
                            // (currently it depends on length)
                            // TODO: Have a better split function
                            Str prefix = SubStr(s1, 0, len);
                            Str suffix1 = DropLeft(s1, len);
                            Str suffix2 = DropLeft(s2, len);
                            tokens[copyIdx - 1] = Concat(prefix, MkUnion([suffix1, suffix2]));
                            continue;
                        }
                    }
                }
                tokens[copyIdx++] = tokens[i];
            }
        }
        if (!constSet.IsEmpty) {
            Debug.Assert(copyIdx < tokens.Count);
            tokens[copyIdx++] = Single(new SetToken(constSet));
        }
        else if (copyIdx == 0)
            return FailStr;
        if (copyIdx == 1)
            return tokens[0];
        tokens.RemoveRange(copyIdx, tokens.Count - copyIdx);
        tokens.Sort();
        return Single(new UnionToken(tokens));
    }

    [Pure]
    static bool StartsWith(Str b, Str other) {
        if (b.Length < other.Length)
            return false;
        // Don't use indexes; the enumerator is faster
        using var e1 = b.GetEnumerator().GetEnumerator();
        using var e2 = other.GetEnumerator().GetEnumerator();
        while (e2.MoveNext()) {
            e1.MoveNext();
            if (!e1.Current.Equals(e2.Current))
                return false;
        }
        return true;
    }

    [Pure]
    static bool EndsWith(Str b, Str other) {
        if (b.Length < other.Length)
            return false;
        using var e1 = b.GetRevEnumerator().GetEnumerator();
        using var e2 = other.GetRevEnumerator().GetEnumerator();
        while (e2.MoveNext()) {
            e1.MoveNext();
            if (!e1.Current.Equals(e2.Current))
                return false;
        }
        return true;
    }

    [Pure]
    static uint CommonPrefix(Str s1, Str s2) {
        using var e1 = s1.GetEnumerator().GetEnumerator();
        using var e2 = s2.GetEnumerator().GetEnumerator();
        uint cnt = 0;
        while (e2.MoveNext()) {
            if (!e1.MoveNext() || !e1.Current.Equals(e2.Current))
                return cnt;
            cnt++;
        }
        return cnt;
    }

    [Pure]
    public Str MkIntersection(List<Str> tokens) {
        if (tokens.IsEmpty())
            return AllStr;
        var subTokens = new List<Str>(tokens.Count);
        foreach (var t in tokens) {
            if (t is SingletonStr { StrToken: IntersectToken u })
                subTokens.AddRange(u.Cases);
            else
                subTokens.Add(t);
        }
        tokens = subTokens;
        tokens.Sort();
        int copyIdx = 0;
        // TODO: Intersect potential single character sets
        // TODO: merge nested intersections
        for (int i = 0; i < tokens.Count; i++) {
            if (copyIdx > 0 && tokens[i].Equals(tokens[copyIdx - 1]))
                continue;
            if (tokens[i].IsFail)
                return FailStr;
            if (tokens[i].IsFull)
                continue;
            tokens[copyIdx++] = tokens[i];
        }
        if (copyIdx == 0)
            return AllStr;
        if (copyIdx == 1)
            return tokens[0];
        tokens.RemoveRange(copyIdx, tokens.Count - copyIdx);
        return Single(new IntersectToken(tokens));
    }

    [Pure]
    public Str MkStar(Str s) {
        if (s.Length == 0)
            return EmptyStr;
        if (s.IsFail)
            return EmptyStr;
        if (s is { Length: 1 }) {
            if (s is { First: KleeneToken k })
                return Single(k);
            if (s is { First: UnionToken u }) {
                // TODO: What about intersection?
                // pretty helpful rewrite:
                // (u_1|...|u_k*|...|u_n)* 
                // => (u_1|...|u_k|...|u_n)*
                // if one of the u_i has a star (is nullable), we can drop top-level stars from all
                var newCases = new List<Str>(u.Cases.Count);
                bool hasKleene = false;
                foreach (var c in u.Cases) {
                    if (c is { Length: 1, First: KleeneToken k2 }) {
                        hasKleene = true;
                        newCases.Add(k2.Base);
                    }
                    else
                        newCases.Add(c);
                }
                // TODO: for other cases as well?
                if (hasKleene)
                    return Single(new KleeneToken(MkUnion(newCases)));
            }
        }
        return Single(new KleeneToken(s));
    }

    [Pure]
    public Str MkPlus(Str s) {
        if (s.Length == 0)
            return EmptyStr;
        if (s is { Length: 1, First: KleeneToken k })
            return Single(k);
        if (s.IsFail)
            return FailStr;
        return Concat(s, Single(new KleeneToken(s)));
    }

    [Pure]
    public Str MkLoop(Str s, uint min, uint max) {
        Debug.Assert(min <= max);
        if (s.Length == 0 || max == 0)
            return EmptyStr;
        if (s.Nullable)
            min = 0;
        if (max == 1) {
            if (min == 1 || s.Nullable)
                return s;
            return MkUnion([EmptyStr, s]);
        }
        if (s is { Length: 1, First: KleeneToken })
            return s;
        return Single(new LoopToken(s, min, max));
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
    public static StrToken[] ToList(Str str) {
        if (str.IsEmpty())
            return [];
        if (str is SingletonStr s)
            return [s.StrToken];
        TupleStr initialStr = (TupleStr)str;
        StrToken[] result;
        if (initialStr.ListCache is not null) {
            if (initialStr.ListCacheFrom == 0 && initialStr.ListCacheTo == (uint)initialStr.ListCache.Length) {
                Stats.CachedStringSequence++;
                return initialStr.ListCache;
            }
            result = new StrToken[(int)str.Length];
            Array.Copy(initialStr.ListCache, initialStr.ListCacheFrom, 
                result, 0, 
                initialStr.ListCacheTo - initialStr.ListCacheFrom);
            initialStr.ListCache = result;
            initialStr.ListCacheFrom = 0;
            initialStr.ListCacheTo = (uint)result.Length;
            return result;
        }
        result = new StrToken[(int)str.Length];
        Stack<(TupleStr str, int from)> todo = [];
        int idx = 0;
        while (true) {
            if (str is TupleStr lts) {
                if (lts.ListCache is not null) {
                    Array.Copy(lts.ListCache, lts.ListCacheFrom, 
                        result, idx,
                        lts.ListCacheTo - lts.ListCacheFrom);
                    idx += (int)(lts.ListCacheTo - lts.ListCacheFrom);
                    continue;
                }
                todo.Push((lts, idx));
                str = lts.Left;
                continue;
            }
            Debug.Assert(str is SingletonStr);
            result[idx++] = ((SingletonStr)str).StrToken;
            if (todo.Count == 0) {
                Debug.Assert(idx == result.Length);
                initialStr.ListCache = result;
                initialStr.ListCacheFrom = 0;
                initialStr.ListCacheTo = (uint)result.Length;
                return result;
            }
            Debug.Assert(todo.Count > 0);
            var (prevStr, prevIdx) = todo.Pop();
            if (prevStr.Left is TupleStr { ListCache: not null } lts2) {
                lts2.ListCache = result;
                lts2.ListCacheFrom = (uint)prevIdx;
                lts2.ListCacheTo = (uint)idx;
                Debug.Assert(lts2.ListCacheTo - lts2.ListCacheFrom == lts2.Length);
            }
            str = prevStr.Right;
        }
    }

    [Pure]
    public Str Simplify(Str str) {
        if (str is EmptyStr)
            return str;
        if (str is SingletonStr s)
            return s.StrToken.OptSimplify(this);

        Debug.Assert(str is TupleStr);
        TupleStr tc = (TupleStr)str;
        if (tc.SimplifyCache is not null) {
            Stats.CachedStringSimplification++;
            return tc.SimplifyCache;
        }
        // TODO: Make iterative
        var left = Simplify(tc.Left);
        var right = Simplify(tc.Right);
        var res = Concat(left, right);
        Debug.Assert(tc.SimplifyCache is null);
        tc.SimplifyCache = res;
        Debug.Assert(res.BalancedTrans);
        return res;
    }

    [Pure]
    public static Expr ToExpr(Str s, Environment env, Dictionary<NamedStrToken, int> currentModificationCnt) {
        if (s.IsEmpty())
            return env.Epsilon;
        using var e = GetRevEnumerator(s).GetEnumerator();
        if (!e.MoveNext()) {
            Debug.Assert(false);
            return env.Epsilon;
        }
        Expr expr = e.Current.ToExpr(env, currentModificationCnt);
        while (e.MoveNext()) {
            expr = env.MkConcat(e.Current.ToExpr(env, currentModificationCnt), expr);
        }
        return expr;
    }
}