using Microsoft.Z3;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.Runtime.CompilerServices;
using System.Text;
using ZIPT.Constraints;
using ZIPT.Strings.Tokens;

namespace ZIPT.Strings.Chunks;

public abstract class Str : IEquatable<Str>, IComparable<Str> {

    public uint ChunkId { get; }
    public abstract uint Length { get; }
    public abstract uint Level { get; }
    public bool Ground { get; protected set; }
    public virtual bool Balanced => true;
    public virtual bool BalancedTrans => true;

    public abstract bool ContainsVar(NamedStrToken v);
    public abstract void CollectVars(HashSet<NamedStrToken> contained);
    public abstract void CollectSymbols(NonTermSet nonTermSet, HashSet<CharToken> alphabet);

    public bool IsEmpty() => Level == 0;
    public bool IsNonEmpty() => Level != 0;
    public bool IsTemp => ChunkId == uint.MaxValue;

    protected Str(uint chunkId) =>
        ChunkId = chunkId;

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

    public int CompareTo(Str? other) {
        if (other is null)
            return 1;
        Debug.Assert(ReferenceEquals(this, other) == (ChunkId == other.ChunkId));
        if (ReferenceEquals(this, other))
            return 0;
        int cmp = Level.CompareTo(other.Level);
        if (cmp != 0)
            return cmp;
        Debug.Assert(GetType() == other.GetType());
        return CompareToInternal(other);
    }

    // Sometimes we need to do a lot of random access - let's convert it to a list for that
    [Pure]
    public abstract IReadOnlyList<StrToken> Sequence();

    protected abstract int CompareToInternal(Str other);

    public abstract override int GetHashCode();

    public abstract bool Equals(Str? other);

    public abstract override bool Equals(object? obj);

    public bool RotationEquals(Str other, uint shift) {
        Debug.Assert(shift > 0 && shift < other.Length);
        if (Length != other.Length)
            return false;
        var enum2 = other.GetEnumerator();
        var enum2r = enum2.GetEnumerator();
        var enum1 = GetEnumerator((uint)shift);
        var enum1r = enum1.GetEnumerator();
        while (enum1r.MoveNext() && enum2r.MoveNext()) {
            if (!enum1r.Current.Equals(enum2r.Current))
                return false;
        }
        enum1r.Dispose();
        enum1 = GetEnumerator();
        enum1r = enum1.GetEnumerator();
        while (enum1r.MoveNext() && enum2r.MoveNext()) {
            if (!enum1r.Current.Equals(enum2r.Current))
                return false;
        }
        enum1r.Dispose();
        enum2r.Dispose();
        return true;
    }

    public IEnumerable<StrToken> GetEnumerator(uint skip = 0) =>
            StrManager.GetEnumerator(this, skip);

    public IEnumerable<StrToken> GetRevEnumerator() =>
        StrManager.GetRevEnumerator(this);


    [MethodImpl(MethodImplOptions.AggressiveInlining), Pure]
    public Expr ToExpr(NielsenGraph graph) =>
        StrManager.ToExpr(this, graph);

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