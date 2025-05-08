using System.Collections;
using System.Diagnostics;
using System.Diagnostics.CodeAnalysis;
using StringBreaker.IntUtils;
using StringBreaker.Tokens;

namespace StringBreaker.MiscUtils;

public class MSet<T, L> : IEnumerable<(T t, L occ)>, IComparable<MSet<T, L>> where T : IComparable<T> where L : IArith<L>, new() {

    // Should not contain zero entries, but might negative ones!!
    protected readonly SortedDictionary<T, L> occurrences;

    static readonly L zero;
    static readonly L one;

    static MSet() {
        zero = new L();
        one = zero.Inc();
    }

    public MSet() =>
        occurrences = [];

    public MSet(MSet<T, L> other) =>
        occurrences = new SortedDictionary<T, L>(other.occurrences);

    public MSet(IReadOnlyCollection<T> s) {
        occurrences = [];
        Add(s);
    }

    public MSet(T s) {
        occurrences = [];
        Add(s);
    }

    public MSet(T s, L occ) {
        occurrences = [];
        Add(s, occ);
    }

    public int Count => occurrences.Count;

    public bool IsEmpty() => occurrences.Count == 0;
    public bool IsNonEmpty() => !IsEmpty();

    public bool Contains(T t) =>
        occurrences.ContainsKey(t);

    public IEnumerator<(T t, L occ)> GetEnumerator() =>
        occurrences.Select(o => (o.Key, o.Value)).GetEnumerator();

    IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();

    public IEnumerable<T> Keys => occurrences.Keys;

    public void Add(T token) => Add(token, one);

    public void Add(T token, L add) {
        if (add.IsZero)
            return;
        if (occurrences.TryGetValue(token, out var count)) {
            var sum = count.Add(add);
            if (sum.IsZero)
                occurrences.Remove(token);
            else
                occurrences[token] = sum;
        }
        else
            occurrences.Add(token, add);
    }

    public void Add(IReadOnlyCollection<T> token) {
        foreach (var t in token) {
            Add(t);
        }
    }

    public void RemoveAll(T t) =>
        occurrences.Remove(t);

    public static void ElimCommon(MSet<T, L> m1, MSet<T, L> m2) {
        using var enum1 = m1.occurrences.GetEnumerator();
        using var enum2 = m2.occurrences.GetEnumerator();
        if (!enum1.MoveNext() || !enum2.MoveNext())
            return;

        List<(T t, L subst)> modification = [];

        do {
            int cmp = enum1.Current.Key.CompareTo(enum2.Current.Key);
            if (cmp == 0) {
                // RemoveAt common subset
                L common = enum1.Current.Value.Min(enum2.Current.Value);
                modification.Add((enum1.Current.Key, common));
                if (!enum1.MoveNext() || !enum2.MoveNext())
                    break;
                continue;
            }
            if (cmp < 0) {
                if (!enum1.MoveNext())
                    break;
            }
            else {
                if (!enum2.MoveNext())
                    break;
            }
        } while (true);

        foreach (var (t, subst) in modification) {
            m1.occurrences[t] = m1.occurrences[t].Sub(subst);
            if (m1.occurrences[t].IsZero)
                m1.occurrences.Remove(t);

            m2.occurrences[t] = m2.occurrences[t].Sub(subst);
            if (m2.occurrences[t].IsZero)
                m2.occurrences.Remove(t);
        }
    }

    public int CompareTo(MSet<T, L>? other) {
        if (other is null)
            return 1;
        if (occurrences.Count > other.occurrences.Count)
            return 1;
        if (occurrences.Count < other.occurrences.Count)
            return -1;
        using var enum1 = occurrences.GetEnumerator();
        using var enum2 = other.occurrences.GetEnumerator();

        if (!enum1.MoveNext() || !enum2.MoveNext())
            return 0;

        do {
            int cmp = enum1.Current.Key.CompareTo(enum2.Current.Key);
            if (cmp != 0)
                return cmp;
            cmp = enum1.Current.Value.CompareTo(enum2.Current.Value);
            if (cmp != 0)
                return cmp;
        } while (enum1.MoveNext() && enum2.MoveNext());

        return 0;
    }

    public override bool Equals(object? obj) =>
        obj is MSet<T, L> set && Equals(set);

    public bool Equals(MSet<T, L> other) {
        if (occurrences.Count != other.occurrences.Count)
            return false;
        var enum1 = occurrences.GetEnumerator();
        var enum2 = other.occurrences.GetEnumerator();
        while (enum1.MoveNext() && enum2.MoveNext()) {
            if (!enum1.Current.Key.Equals(enum2.Current.Key) || !enum1.Current.Value.Equals(enum2.Current.Value))
                return false;
        }
        Debug.Assert(!enum1.MoveNext() && !enum2.MoveNext());
        return true;
    }

    public override int GetHashCode() =>
        occurrences.Aggregate(439852997,
            (acc, kv) => acc * 743032429 + kv.Key.GetHashCode() * 689001223 + kv.Value.GetHashCode());

    // Note: Multi-Sets are not totally ordered. i.e., !(A <= B) =/=> A > B
    public bool IsSubset(MSet<T, L> other) {
        if (other.occurrences.Count < occurrences.Count)
            return false;
        bool proper = other.occurrences.Count > occurrences.Count;
        foreach (var kv in occurrences) {
            if (!other.occurrences.TryGetValue(kv.Key, out var count) || count.LessThan(kv.Value))
                return false;
            proper |= kv.Value.LessThan(count);
        }
        return proper;
    }

    public bool IsSubsetEq(MSet<T, L> other) {
        if (other.occurrences.Count < occurrences.Count)
            return false;
        foreach (var kv in occurrences) {
            if (!other.occurrences.TryGetValue(kv.Key, out var count) || count.LessThan(kv.Value))
                return false;
        }
        return true;
    }

    public MSet<T, L>? Subtraction(MSet<T, L> other) {
        if (other.Count > Count)
            return null;
        MSet<T, L> ret = new();
        int found = 0;
        foreach (var kv in occurrences) {
            if (!other.occurrences.TryGetValue(kv.Key, out var count) || count.LessThan(kv.Value))
                return null;
            if (count.IsPos)
                found++;
            if (kv.Value.LessThan(count))
                ret.Add(kv.Key, count.Sub(kv.Value));
        }
        return found != other.occurrences.Count ? null : ret;
    }

    public bool IsSingleVar([NotNullWhen(true)] out StrVarToken? varToken) =>
        IsSingleVar(out varToken, out L m) && m.IsOne;

    public bool IsSingleVar([NotNullWhen(true)] out StrVarToken? varToken, out L m) {
        if (occurrences.Count != 1) {
            varToken = null;
            m = new L();
            return false;
        }
        var first = occurrences.First();
        if (first.Key is not StrVarToken v) {
            varToken = null;
            m = new L();
            return false;
        }
        varToken = v;
        m = first.Value;
        return true;
    }

    public MSet<T, L> Clone() => new(this);

    public override string ToString() =>
        "{{ " + string.Join(", ", occurrences.Select(kv => $"{kv.Key}^{kv.Value}")) + " }}";
}