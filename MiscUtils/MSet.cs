using System.Collections;
using System.Diagnostics;
using System.Diagnostics.CodeAnalysis;
using StringBreaker.Constraints;
using StringBreaker.IntUtils;
using StringBreaker.Tokens;

namespace StringBreaker.MiscUtils;

public class MSet<T> : IEnumerable<(T t, Len occ)>, IComparable<MSet<T>> where T : IComparable<T> {

    // Should not contain zero entries, but might negative ones!!
    readonly SortedDictionary<T, Len> occurrences;

    public MSet() =>
        occurrences = [];

    public MSet(MSet<T> other) =>
        occurrences = new SortedDictionary<T, Len>(other.occurrences);

    public MSet(IReadOnlyCollection<T> s) {
        occurrences = [];
        Add(s);
    }

    public MSet(T s) {
        occurrences = [];
        Add(s);
    }

    public int Count => occurrences.Count;

    public bool IsEmpty() => occurrences.Count == 0;
    public bool IsNonEmpty() => !IsEmpty();

    public bool Contains(T t) =>
        occurrences.ContainsKey(t);

    public IEnumerator<(T t, Len occ)> GetEnumerator() =>
        occurrences.Select(o => (o.Key, o.Value)).GetEnumerator();

    IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();

    public IEnumerable<T> Keys => occurrences.Keys;

    public void Add(T token) => Add(token, 1);

    public void Add(T token, Len add) {
        if (occurrences.TryGetValue(token, out var count)) {
            if (count + add == 0)
                occurrences.Remove(token);
            else
                occurrences[token] = count + add;
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

    public static void ElimCommon(MSet<T> m1, MSet<T> m2) {
        using var enum1 = m1.occurrences.GetEnumerator();
        using var enum2 = m2.occurrences.GetEnumerator();
        if (!enum1.MoveNext() || !enum2.MoveNext())
            return;

        List<(T t, Len subst)> modification = [];

        do {
            int cmp = enum1.Current.Key.CompareTo(enum2.Current.Key);
            if (cmp == 0) {
                // RemoveAt common subset
                Len common = Len.Min(enum1.Current.Value, enum2.Current.Value);
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
            var newVal = m1.occurrences[t] -= subst;
            if (newVal == 0)
                m1.occurrences.Remove(t);
            newVal = m2.occurrences[t] -= subst;
            if (newVal == 0)
                m2.occurrences.Remove(t);
        }
    }

    public int CompareTo(MSet<T>? other) {
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
        obj is MSet<T> set && Equals(set);

    public bool Equals(MSet<T> other) {
        if (occurrences.Count != other.occurrences.Count)
            return false;
        var enum1 = occurrences.GetEnumerator();
        var enum2 = other.occurrences.GetEnumerator();
        while (enum1.MoveNext() && enum2.MoveNext()) {
            if (!enum1.Current.Key.Equals(enum2.Current.Key) || enum1.Current.Value != enum2.Current.Value)
                return false;
        }
        Debug.Assert(!enum1.MoveNext() && !enum2.MoveNext());
        return true;
    }

    public override int GetHashCode() =>
        occurrences.Aggregate(439852997,
            (acc, kv) => acc * 743032429 + kv.Key.GetHashCode() * 689001223 + kv.Value.GetHashCode());

    // Note: Multi-Sets are not totally ordered. i.e., !(A <= B) =/=> A > B
    public bool IsSubset(MSet<T> other) {
        if (other.occurrences.Count < occurrences.Count)
            return false;
        bool proper = other.occurrences.Count > occurrences.Count;
        foreach (var kv in occurrences) {
            if (!other.occurrences.TryGetValue(kv.Key, out var count) || count < kv.Value)
                return false;
            proper |= count > kv.Value;
        }
        return proper;
    }

    public bool IsSubsetEq(MSet<T> other) {
        if (other.occurrences.Count < occurrences.Count)
            return false;
        foreach (var kv in occurrences) {
            if (!other.occurrences.TryGetValue(kv.Key, out var count) || count < kv.Value)
                return false;
        }
        return true;
    }

    public MSet<T>? Subtraction(MSet<T> other) {
        if (other.Count > Count)
            return null;
        MSet<T> ret = new();
        int found = 0;
        foreach (var kv in occurrences) {
            if (!other.occurrences.TryGetValue(kv.Key, out var count) || count < kv.Value)
                return null;
            if (count > 0)
                found++;
            if (count > kv.Value)
                ret.Add(kv.Key, count - kv.Value);
        }
        return found != other.occurrences.Count ? null : ret;
    }

    public bool IsSingleVar([NotNullWhen(true)] out StrVarToken? varToken) =>
        IsSingleVar(out varToken, out Len mult) && mult == 1;

    public bool IsSingleVar([NotNullWhen(true)] out StrVarToken? varToken, out Len mult) {
        if (occurrences.Count != 1) {
            varToken = null;
            mult = 0;
            return false;
        }
        var first = occurrences.First();
        if (first.Key is not StrVarToken v) {
            varToken = null;
            mult = 0;
            return false;
        }
        varToken = v;
        mult = first.Value;
        return true;
    }

    public MSet<T> Clone() => new(this);

    public override string ToString() =>
        "{{ " + string.Join(", ", occurrences.Select(kv => $"{kv.Key}^{kv.Value}")) + " }}";
}