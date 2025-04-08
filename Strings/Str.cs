using System.Collections;
using Microsoft.Z3;
using System.Diagnostics;
using System.Runtime.CompilerServices;
using StringBreaker.Constraints;

namespace StringBreaker.Strings;

public class Str : IComparable<Str>, IReadOnlyCollection<StrTokenRef> {

    List<StrTokenRef> Data { get; }

    public int Count => Data.Count;

    public Str() => Data = [];

    public Str(IEnumerable<StrTokenRef> val) => Data = val.ToList();

    public Str(params StrTokenRef[] val) => Data = val.ToList();

    public Str(int capacity) {
        capacity = Math.Max(capacity, 1);
        Data = new List<StrTokenRef>(capacity);
    }

    public Str(NielsenContext ctx, StrRef fromIt, StrRef toIt, IList<StrTokenRef> attach, bool dir, int cap = 0) : this(cap) {
        if (dir) {
            while (true) {
                fromIt.MoveInLeft(ctx);
                toIt.MoveInLeft(ctx);
                if (fromIt.Equals(toIt))
                    break;
                Add(fromIt.SkipFirst(ctx));
            }
            AddRange(attach);
            return;
        }
        AddRangeRev(attach);
        while (true) {
            fromIt.MoveInRight(ctx);
            toIt.MoveInRight(ctx);
            if (fromIt.Equals(toIt))
                break;
            Add(fromIt.SkipFirst(ctx));
        }
    }

    public StrTokenRef this[int idx]
    {
        get
        {
            Debug.Assert(idx < Data.Count);
            return Data[idx];
        }
        set
        {
            Debug.Assert(idx < Data.Count);
            Data[idx] = value;
        }
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public StrRef ToRef() => new(this);

    public void Add(StrTokenRef item) => Data.Add(item);

    public void AddRange(IList<StrTokenRef> toAdd) => Data.AddRange(toAdd);
    public void AddRangeRev(IList<StrTokenRef> toAdd) {
        Data.EnsureCapacity(Data.Count + toAdd.Count);
        for (int i = 0; i < toAdd.Count; i++) {
            Data.Add(toAdd[toAdd.Count - 1 - i]);
        }
    }

    public void AddRange(Str toAdd) => Data.AddRange(toAdd.Data);

    public IEnumerator<StrTokenRef> GetEnumerator() => Data.GetEnumerator();

    IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();

    public Expr ToExpr(NielsenContext ctx) {
        if (Count == 0)
            return ctx.Cache.Epsilon;
        Expr last = this[^1].ToExpr(ctx);
        for (int i = Count - 1; i > 0; i--) {
            last = ctx.Cache.MkConcat(this[i - 1].ToExpr(ctx), last);
        }
        return last;
    }

    /*public override bool Equals(object? obj) =>
        obj is Str other && Equals(other);

    public bool Equals(Str other) =>
        Count == other.Count && this.SequenceEqual(other);

    public override int GetHashCode() =>
        this.Aggregate(387815837, (current, token) => current * 941706509 + token.GetHashCode());*/

    // Deliberately only comparing references (compare the StrRef for actual comparison!)
    public override bool Equals(object? obj) => ReferenceEquals(this, obj);
    public override int GetHashCode() => base.GetHashCode();

    public override string ToString() =>
        Count == 0 ? "ε" : string.Concat(this.Select(o => o.ToString()));

    public Str ShallowClone() => new(Data);

    public int CompareTo(Str? other) {
        if (other is null || Count > other.Count)
            return 1;
        if (Count < other.Count)
            return -1;
        for (int i = 0; i < Count; i++) {
            switch (this[i].CompareTo(other[i])) {
                case < 0:
                    return -1;
                case > 0:
                    return 1;
            }
        }
        return 0;
    }
}