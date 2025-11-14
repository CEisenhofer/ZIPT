using Microsoft.Z3;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.Runtime.CompilerServices;
using System.Text;
using ZIPT.Constraints;
using ZIPT.MiscUtils;
using ZIPT.Strings.Tokens;
using ZIPT.Strings.Tokens.RegexTokens;

namespace ZIPT.Strings.Chunks;

public abstract class Str : IEquatable<Str>, IComparable<Str> {

    public uint ChunkId { get; }
    public abstract uint Length { get; }
    public abstract uint Level { get; }
    public bool Ground { get; protected set; }
    public bool RegexFree { get; protected set; }
    public bool Derivable { get; protected set; }
    public bool Nullable { get; protected set; }
    public bool BasicRegex { get; protected set; }
    public virtual bool Balanced => true;
    public virtual bool BalancedTrans => true;

    protected Dictionary<CharacterSet, Str>? derivativeSetCacheFwd;
    protected Dictionary<CharacterSet, Str>? derivativeSetCacheBwd;

    Str normalised;

    public Str Normalised
    {
        get
        {
            while (!ReferenceEquals(normalised, normalised.normalised)) {
                normalised = normalised.normalised;
            }
            return normalised;
        }
        set
        {
            if (IsNormalised && !ReferenceEquals(this, value))
                value.MoveCache(this);
            normalised = value;
        }
    } // a representative for all equal strings [mostly this is itself; also it can change]; not normalised strings to avoid degenerated strings
    public bool IsNormalised => ReferenceEquals(this, Normalised); // If two strings are normalised then they are equal iff they have equal references
    public int DegenerationLevel { get; protected set; } // value for how much the datastructure is away from a balanced tree
    public bool IsDegenerated => DegenerationLevel >= Options.MaxDegenerationLevel;

    public abstract bool ContainsVar(NamedStrToken v);
    public abstract bool ContainsSChar(SymCharToken v);
    public abstract void CollectVars(HashSet<NamedStrToken> contained);
    public abstract void CollectSChars(HashSet<SymCharToken> contained);
    public abstract void CollectSymbols(NonTermSet nonTermSet, CharacterSet alphabet);
    public abstract HashSet<NamedStrToken> ContainedVars();
    public abstract MinTerms FirstMinTerms();
    public abstract MinTerms LastMinTerms();

    public bool IsEmpty() => Level == 0;
    public bool IsNonEmpty() => Level != 0;
    public bool IsTemp => ChunkId == uint.MaxValue;
    public bool IsFail => this is SingletonStr { StrToken: FailToken };
    public bool IsFull => this is SingletonStr { StrToken: KleeneToken { Base: SingletonStr { StrToken: SetToken { Set.IsFull: true } } } };

    protected Str(uint chunkId) {
        ChunkId = chunkId;
        normalised = this;
    }

    public StrToken this[bool fwd, uint idx]
    {
        [MethodImpl(MethodImplOptions.AggressiveInlining), Pure]
        get => StrManager.GetIndex(this, idx, fwd);
    }

    public StrToken this[bool fwd, int idx]
    {
        [MethodImpl(MethodImplOptions.AggressiveInlining), Pure]
        get
        {
            Debug.Assert(idx >= 0);
            return StrManager.GetIndex(this, (uint)idx, fwd);
        }
    }

    public StrToken this[uint idx] {
        [MethodImpl(MethodImplOptions.AggressiveInlining), Pure]
        get => StrManager.GetIndex(this, idx, true);
    }

    public StrToken this[int idx]
    {
        [MethodImpl(MethodImplOptions.AggressiveInlining), Pure]
        get
        {
            Debug.Assert(idx >= 0);
            return StrManager.GetIndex(this, (uint)idx, true);
        }
    }

    public StrToken this[bool fwd]
    {
        [MethodImpl(MethodImplOptions.AggressiveInlining), Pure]
        get => StrManager.GetIndex(this, 0, fwd);
    }

    // TODO: Cache?
    public StrToken First
    {
        [MethodImpl(MethodImplOptions.AggressiveInlining), Pure]
        get => StrManager.GetIndex(this, 0, true);
    }

    public StrToken Last
    {
        [MethodImpl(MethodImplOptions.AggressiveInlining), Pure]
        get => StrManager.GetIndex(this, 0, false);
    }


    public abstract Str Translate(StrManager manager);

    public int CompareTo(Str? other, bool fwd) {
        if (other is null)
            return 1;
        Debug.Assert(ReferenceEquals(this, other) == (ChunkId == other.ChunkId));
        if (ReferenceEquals(this, other))
            return 0;
        if (Length < other.Length)
            return -1;
        if (Length > other.Length)
            return 1;
        using var enum1 = fwd ? GetEnumerator().GetEnumerator() : GetRevEnumerator().GetEnumerator();
        using var enum2 = fwd ? other.GetEnumerator().GetEnumerator() : other.GetRevEnumerator().GetEnumerator();
        while (enum1.MoveNext() && enum2.MoveNext()) {
            int cmp = enum1.Current.CompareTo(enum2.Current);
            if (cmp != 0)
                return cmp;
        }
        return 0;
    }

    public int CompareTo(Str? other) => CompareTo(other, true);

    public abstract override int GetHashCode();

    public abstract bool Equals(Str? other);

    public abstract override bool Equals(object? obj);

    public static bool CachedEquals(Str s1, Str s2) =>
        ReferenceEquals(s1.Normalised, s2.Normalised);

    public bool CachedEquals(Str other) =>
        CachedEquals(this, other);

    public bool RotationEquals(Str other, uint shift) {
        Debug.Assert(shift > 0 && shift < other.Length);
        if (Length != other.Length)
            return false;
        var enum2 = other.GetEnumerator();
        var enum2R = enum2.GetEnumerator();
        var enum1 = GetEnumerator(shift);
        var enum1R = enum1.GetEnumerator();
        while (enum1R.MoveNext() && enum2R.MoveNext()) {
            if (!enum1R.Current.Equals(enum2R.Current))
                return false;
        }
        enum1R.Dispose();
        enum1 = GetEnumerator();
        enum1R = enum1.GetEnumerator();
        while (enum1R.MoveNext() && enum2R.MoveNext()) {
            if (!enum1R.Current.Equals(enum2R.Current))
                return false;
        }
        enum1R.Dispose();
        enum2R.Dispose();
        return true;
    }

    public IEnumerable<StrToken> GetEnumerator(uint skip = 0) =>
            StrManager.GetEnumerator(this, skip);

    public IEnumerable<StrToken> GetRevEnumerator() =>
        StrManager.GetRevEnumerator(this);

    public StrToken[] ToArray() =>
        StrManager.ToList(this);

    [MethodImpl(MethodImplOptions.AggressiveInlining), Pure]
    public Expr ToExpr(LocalInfo info) => ToExpr(info.Env, info.CurrentModificationCnt);

    [MethodImpl(MethodImplOptions.AggressiveInlining), Pure]
    public Expr ToExpr(Environment env, Dictionary<NamedStrToken, int> currentModificationCnt) =>
        StrManager.ToExpr(this, env, currentModificationCnt);

    public abstract void MoveCache(Str old);

    public Str Derivative(Environment env, CharToken a, bool fwd) => 
        Derivative(env, new CharacterSet(new CharacterRange(a.Value)), fwd);
    public abstract Str Derivative(Environment env, CharacterSet a, bool fwd);

    public string ToDot() {
        StringBuilder sb = new();
        HashSet<Str> visited = new HashSet<Str>(ReferenceEqualityComparer.Instance);
        Stack<Str> toDo = [];
        toDo.Push(this);
        Dictionary<Str, uint> chunkToId = new Dictionary<Str, uint>(ReferenceEqualityComparer.Instance);
        sb.AppendLine("digraph G {");
        while (toDo.Count > 0) {
            Str current = toDo.Pop();
            if (!visited.Add(current))
                continue;
            if (!chunkToId.TryGetValue(current, out uint fromId))
                chunkToId.Add(current, fromId = (uint)chunkToId.Count);
            sb.Append("  ").Append(fromId).Append(" [label=\"").Append(current.RawString).Append(" - ").Append(current.Level).AppendLine("\"];");
            if (current is not TupleStr tuple)
                continue;
            if (!chunkToId.TryGetValue(tuple.Left, out uint leftId))
                chunkToId.Add(tuple.Left, leftId = (uint)chunkToId.Count);
            if (!chunkToId.TryGetValue(tuple.Right, out uint rightId))
                chunkToId.Add(tuple.Right, rightId = (uint)chunkToId.Count);

            sb.Append("  ").Append(fromId).Append(" -> ").Append(leftId).AppendLine(" [label=<LHS>];");
            sb.Append("  ").Append(fromId).Append(" -> ").Append(rightId).AppendLine(" [label=<RHS>];");
            toDo.Push(tuple.Left);
            toDo.Push(tuple.Right);
        }
        sb.AppendLine("}");
        return sb.ToString();
    }

    public abstract string RawString { get; }
    public string PlainString => GetPlainString(null);

    [Pure]
    public abstract string GetPlainString(NielsenGraph? node);

    public sealed override string ToString() => PlainString;
    public string ToString(NielsenGraph? graph) => GetPlainString(graph);
}