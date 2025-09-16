using Microsoft.Z3;
using System.Collections;
using System.Collections.Specialized;
using System.Diagnostics;
using System.Runtime.CompilerServices;
using ZIPT.Constraints;
using ZIPT.IntUtils;
using ZIPT.Strings.Chunks;
using ZIPT.Strings.Tokens;

namespace ZIPT.Strings;

#if false
public class OStr : IEquatable<OStr>, IComparable<OStr>, IReadOnlyList<StrToken> {

    public readonly IdSet VarOccurrences;
    Dictionary<StrVarToken, PDD>? varCountsCache;
    Dictionary<CharToken, PDD>? charCountsCache;
    public IReadOnlyList<OChunk> Chunks { get; }
    public uint Length { get; }
    public int Count => (int)Length;
    public bool IsEmpty => Length == 0;
    public bool IsNonEmpty => !IsEmpty;

    readonly int hashCode;

    public OStr(IReadOnlyList<OChunk> chunks, uint len) {
        Debug.Assert(len == chunks.Sum(o => o.Length));
        Chunks = chunks;
        Length = len;
        VarOccurrences = new IdSet();
        foreach (var chunk in chunks) {
            chunk.OrIn(ref VarOccurrences);
        }
        hashCode = ComputeHashCode();
    }

    public OStr(IReadOnlyList<OChunk> chunks) : this(chunks, (uint)chunks.Sum(c => c.Length)) { }

    public StrToken this[int idx] {
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        get => PeekFrwd(idx);
    }

    public StrToken this[bool frwd] {
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        get => frwd ? PeekFrwd(0) : PeekBkwd(0);
    }

    public StrToken this[bool frwd, int idx] {
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        get => frwd ? PeekFrwd(idx) : PeekBkwd(idx);
    }

    public bool Contains(NamedStrToken v) => 
        VarOccurrences.Contains(v.StrVarId);

    public OStr Apply(Interpretation itp) {
        List<OChunk> newChunks = [];
        foreach (var chunk in Chunks) {
            newChunks.AddRange(chunk.Apply(itp));
        }
        return new OStr(newChunks);
    }

    StrToken PeekFrwd(int idx) {
        Debug.Assert(idx >= 0 && idx < Length);
        foreach (var chunk in Chunks) {
            if (idx < chunk.Length)
                return chunk[idx];
            idx -= chunk.Length;
        }
        throw new IndexOutOfRangeException($"Index {idx} is out of bounds for string of length {Length}");
    }

    StrToken PeekBkwd(int idx) {
        Debug.Assert(idx >= 0 && idx < Length);
        for (int i = Chunks.Count; i > 0; i--) {
            var chunk = Chunks[i - 1];
            if (idx < chunk.Length)
                return chunk[chunk.Length - idx - 1];
            idx -= chunk.Length;
        }
        throw new IndexOutOfRangeException($"Index {idx} is out of bounds for string of length {Length}");
    }

    public bool IsNullable(NielsenNode node) => this.All(token => token.IsNullable(node));

    public void CollectSymbols(NonTermSet nonTermSet, HashSet<CharToken> alphabet) {
        foreach (var token in this) {
            switch (token) {
                case NamedStrToken v:
                    nonTermSet.Add(v);
                    break;
                case CharToken c:
                    alphabet.Add(c);
                    break;
                case SymCharToken s:
                    nonTermSet.Add(s);
                    break;
                case PowerToken p:
                    p.Base.CollectSymbols(nonTermSet, alphabet);
                    p.Power.CollectSymbols(nonTermSet, alphabet);
                    break;
                default:
                    throw new NotSupportedException();
            }
        }
    }

    public void GetOcc(
        out Dictionary<StrVarToken, PDD> varCounts,
        out Dictionary<CharToken, PDD> charCounts) {

        if (varCountsCache is not null) {
            Debug.Assert(charCountsCache is not null);
            varCounts = varCountsCache;
            charCounts = charCountsCache;
            return;
        }
        varCounts = [];
        charCounts = [];
        foreach (var chunk in Chunks) {
            chunk.AddOcc(varCounts, charCounts);
        }
        varCountsCache = varCounts;
        charCountsCache = charCounts;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public OStr Drop(bool frwd, Environment env) =>
        frwd ? DropForward(env) : DropBackwards(env);

#if false
    public OStr DropForward(Environment env, uint frwd, uint bkwd) {
        Debug.Assert(frwd + bkwd < Length);
        if (frwd == 0 && bkwd == 0)
            return this;
        var varCounts = VarCounts;
        var charCounts = CharCounts;
        int fromChunk = 0;
        int toChunk = 0;
        for (int i = 0; i < Chunks.Count; i++) {
            var chunk = Chunks[i];
            if (frwd < chunk.Length) {
                fromChunk = i;
                break;
            }
            frwd = (uint)(frwd - chunk.Length);
            chunk.DropAll();
        }
        for (int i = Chunks.Count; i > 0; i--) {
            var chunk = Chunks[i - 1];
            if (bkwd < chunk.Length) {
                toChunk = i;
                break;
            }
            bkwd = (uint)(bkwd - chunk.Length);
        }
        if (fromChunk == toChunk)
            return new OStr([Chunks[fromChunk].Extract(fromChunk, Chunks[fromChunk].Length - fromChunk, env)]);
        Debug.Assert(fromChunk < toChunk);
        Chunk[] chunks = new Chunk[toChunk - fromChunk + 1];
        int diff = toChunk - fromChunk - 1;
        Debug.Assert(diff >= 0);
        chunks[0] = Chunks[fromChunk].Extract((int)frwd, Chunks[fromChunk].Length, env);
        for (int i = 0; i < diff; i++) {
            chunks[i + 1] = Chunks[fromChunk + 1];
        }
        chunks[diff + 1] = Chunks[toChunk].Extract(0, Chunks[toChunk].Length - (int)frwd, env);
        return new OStr(chunks, );
    }
#endif

    public OStr DropForward(Environment env) {
        Debug.Assert(Chunks.Count > 0);
        var newFirst = Chunks[0].DropFirst(env);
        OChunk[] chunks;
        if (newFirst.IsEmpty()) {
            chunks = new OChunk[Chunks.Count - 1];
            for (int i = 1; i < Chunks.Count; i++) {
                chunks[i - 1] = Chunks[i];
            }
        }
        else {
            chunks = new OChunk[Chunks.Count];
            chunks[0] = newFirst;
            for (int i = 1; i < Chunks.Count; i++) {
                chunks[i] = Chunks[i];
            }
        }
        return new OStr(chunks, Length - 1);
    }

    public OStr DropBackwards(Environment env) {
        Debug.Assert(Chunks.Count > 0);
        var newLast = Chunks[^1].DropLast(env);
        OChunk[] chunks;
        if (newLast.IsEmpty()) {
            chunks = new OChunk[Chunks.Count - 1];
            for (int i = 0; i < Chunks.Count - 1; i++) {
                chunks[i] = Chunks[i];
            }
        }
        else {
            chunks = new OChunk[Chunks.Count];
            for (int i = 0; i < Chunks.Count - 1; i++) {
                chunks[i] = Chunks[i];
            }
            chunks[^1] = newLast;
        }
        return new OStr(chunks, Length - 1);
    }

    public OStr SubstX(StrVarToken x, Environment env) {
        if (!VarOccurrences.Contains(x.StrVarId))
            return this;
        List<OChunk> newChunks = new(Chunks.Count);
        foreach (var chunk in Chunks) {
            chunk.SubstX(x, env);
            if (chunk.IsEmpty())
                continue;
            newChunks.Add(chunk);
        }
        return new OStr(newChunks.ToArray());
    }

    public OStr SubstAX(bool frwd, StrVarToken x, CharToken a, Environment env) =>
        frwd ? SubstAX(x, a, env) : SubstXA(x, a, env);

    public OStr SubstXA(StrVarToken x, CharToken a, Environment env) {
        if (!VarOccurrences.Contains(x.StrVarId))
            return this;
        var newChunks = new OChunk[Chunks.Count];
        for (int i = 0; i < Chunks.Count; i++) {
            OChunk c = Chunks[i].SubstXA(x, a, env);
            newChunks[i] = c;
        }
        return new OStr(newChunks);
    }

    public OStr SubstAX(StrVarToken x, CharToken a, Environment env) {
        if (!VarOccurrences.Contains(x.StrVarId))
            return this;
        var newChunks = new OChunk[Chunks.Count];
        for (int i = 0; i < Chunks.Count; i++) {
            OChunk c = Chunks[i].SubstAX(x, a, env);
            newChunks[i] = c;
        }
        return new OStr(newChunks);
    }

    public OStr SubstYX(bool frwd, StrVarToken x, StrVarToken y, Environment env) =>
            frwd ? SubstYX(x, y, env) : SubstXY(x, y, env);

    public OStr SubstXY(StrVarToken x, StrVarToken y, Environment env) {
        if (!VarOccurrences.Contains(x.StrVarId))
            return this;
        var newChunks = new List<OChunk>(Chunks.Count + 2);
        for (int i = 0; i < Chunks.Count; i++) {
            var c = Chunks[i].SubstXY(x, y, env);
            Debug.Assert(c.Length <= 2);
            foreach (var chunk in c) {
                newChunks.Add(chunk);
            }
        }
        return new OStr(newChunks);
    }

    public OStr SubstYX(StrVarToken x, StrVarToken y, Environment env) {
        if (!VarOccurrences.Contains(x.StrVarId))
            return this;
        var newChunks = new List<OChunk>(Chunks.Count + 2);
        for (int i = 0; i < Chunks.Count; i++) {
            var c = Chunks[i].SubstYX(x, y, env);
            Debug.Assert(c.Length <= 2);
            foreach (var chunk in c) {
                newChunks.Add(chunk);
            }
        }
        return new OStr(newChunks);
    }


    public OStr Unwind(bool dir, NielsenNode node) =>
        dir ? UnwindFrwd(node) : UnwindBkwd(node);

    public OStr UnwindFrwd(NielsenNode node) {
        Debug.Assert(Chunks.Count > 0);
        var cases = Chunks[0].UnwindFrwd(node);
        OChunk[] newChunks = new OChunk[Chunks.Count + cases.Length - 1];
        int j = 0;
        for (; j < newChunks.Length; j++) {
            newChunks[j] = cases[j];
        }
        for (int i = 1; i < Chunks.Count; i++) {
            newChunks[j++] = Chunks[i];
        }
        Debug.Assert(j == Chunks.Count);
        return new OStr(newChunks, Length);
    }

    public OStr UnwindBkwd(NielsenNode node) {
        Debug.Assert(Chunks.Count > 0);
        var cases = Chunks[^1].UnwindBkwd(node);
        OChunk[] newChunks = new OChunk[Chunks.Count + cases.Length - 1];
        int j = 0;
        for (int i = 0; i < Chunks.Count - 1; i++) {
            newChunks[j++] = Chunks[i];
        }
        for (int i = 0; j < newChunks.Length; j++) {
            newChunks[j] = cases[i++];
        }
        Debug.Assert(j == Chunks.Count);
        return new OStr(newChunks);
    }

    public IEnumerator<StrToken> GetEnumerator() {
        foreach (var chunk in Chunks) {
            foreach (var token in chunk) {
                yield return token;
            }
        }
    }

    public override bool Equals(object? obj) =>
        obj is OStr other && Equals(other);

    public bool Equals(OStr? other) {
        if (other is null)
            return false;
        if (ReferenceEquals(this, other))
            return true;
        if (Length != other.Length)
            return false;
        if (hashCode != other.hashCode)
            return false;
        using var e1 = GetEnumerator();
        using var e2 = other.GetEnumerator();
        while (e1.MoveNext() && e2.MoveNext()) {
            if (!e1.Current.Equals(e2.Current))
                return false;
        }
        Debug.Assert(!e1.MoveNext() && !e2.MoveNext());
        return true;
    }

    int ComputeHashCode() =>
        Chunks.Aggregate(566652221, (hash, chunk) => 130503733 * hash + chunk.GetHashCode());

    public override int GetHashCode() => hashCode;

    public int CompareTo(OStr? other) {
        if (other is null)
            return 1;
        if (ReferenceEquals(this, other))
            return 0;
        if (Length != other.Length)
            return Length.CompareTo(other.Length);
        using var e1 = GetEnumerator();
        using var e2 = other.GetEnumerator();
        while (e1.MoveNext() && e2.MoveNext()) {
            int cmp = e1.Current.CompareTo(e2.Current);
            if (cmp != 0)
                return cmp;
        }
        Debug.Assert(!e1.MoveNext() && !e2.MoveNext());
        return 0;
    }

    // public MSet<StrToken, BigInteger> ToSet() => new(this);

    public Expr ToExpr(NielsenGraph graph) {
        if (IsEmpty())
            return graph.Env.Epsilon;
        Expr last = Chunks[^1].ToExpr(graph);
        for (int i = Chunks.Count - 1; i > 0; i--) {
            last = graph.Env.MkConcat(Chunks[i - 1].ToExpr(graph), last);
        }
        return last;
    }

    public override string ToString() => string.Concat(Chunks.Select(o => o.ToString()));
    public string ToString(NielsenGraph graph) => string.Concat(Chunks.Select(o => o.ToString(graph)));
    IEnumerator IEnumerable.GetEnumerator() =>
        GetEnumerator();
}
#endif