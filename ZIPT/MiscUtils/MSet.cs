using System.Collections;
using System.Diagnostics;
using System.Numerics;
using ZIPT.IntUtils;

namespace ZIPT.MiscUtils;

public class MSet<T> : IEnumerable<(T t, PDD<BigInteger> occ)>, IComparable<MSet<T>> where T : IComparable<T> {

    // Should not contain zero entries, but might negative ones!!
    readonly SortedDictionary<T, PDD<BigInteger>> occurrences;
    PDD<BigInteger>.PDDManager Manager { get; }

    public MSet(PDD<BigInteger>.PDDManager manager) {
        occurrences = [];
        Manager = manager;
    }

    public MSet(MSet<T> other) {
        occurrences = new SortedDictionary<T, PDD<BigInteger>>(other.occurrences);
        Manager = other.Manager;
    }

    public MSet(PDD<BigInteger>.PDDManager manager, IReadOnlyCollection<T> s) {
        Manager = manager;
        occurrences = [];
        Add(s);
    }

    public MSet(PDD<BigInteger>.PDDManager manager, T s) {
        Manager = manager;
        occurrences = [];
        Add(s);
    }

    public MSet(T s, PDD<BigInteger> occ) {
        Manager = occ.Manager;
        occurrences = [];
        Add(s, occ);
    }

    public int Count => occurrences.Count;

    public bool IsEmpty() => occurrences.Count == 0;
    public bool IsNonEmpty() => !IsEmpty();

    public bool Contains(T t) =>
        occurrences.ContainsKey(t);

    public IEnumerator<(T t, PDD<BigInteger> occ)> GetEnumerator() =>
        occurrences.Select(o => (o.Key, o.Value)).GetEnumerator();

    IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();

    public IEnumerable<T> Keys => occurrences.Keys;

    public void Add(T token) => Add(token, Manager.One);

    public void Add(T token, PDD<BigInteger> add) {
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

    /*public static void ElimCommon(MSet<T> m1, MSet<T> m2) {
        using var enum1 = m1.occurrences.GetEnumerator();
        using var enum2 = m2.occurrences.GetEnumerator();
        if (!enum1.MoveNext() || !enum2.MoveNext())
            return;

        List<(T t, PDD<BigInteger> subst)> modification = [];

        do {
            int cmp = enum1.Current.Key.CompareTo(enum2.Current.Key);
            if (cmp == 0) {
                // RemoveAt common subset
                PDD<BigInteger> sub = enum1.Current.Value.Sub(enum2.Current.Value);
                int s = sub.GetPolarity();
                PDD<BigInteger> common = enum1.Current.Value.Min(enum2.Current.Value);
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
    }*/

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
    public bool IsSubset(MSet<T> other) {
        if (other.occurrences.Count < occurrences.Count)
            return false;
        bool proper = other.occurrences.Count > occurrences.Count;
        foreach (var kv in occurrences) {
            if (!other.occurrences.TryGetValue(kv.Key, out var count))
                return false;
            PDD<BigInteger> sub = count.Sub(kv.Value);
            int sig = PDD<BigInteger>.GetPolarity(sub);
            if (sig != -1)
                return false;
            proper |= !sub.IsZero;
        }
        return proper;
    }

    public bool IsSubsetEq(MSet<T> other) {
        if (other.occurrences.Count < occurrences.Count)
            return false;
        foreach (var kv in occurrences) {
            if (!other.occurrences.TryGetValue(kv.Key, out var count))
                return false;
            PDD<BigInteger> sub = count.Sub(kv.Value);
            int sig = PDD<BigInteger>.GetPolarity(sub);
            if (sig != -1)
                return false;
        }
        return true;
    }

    public MSet<T> Clone() => new(this);

    public override string ToString() =>
        "{{ " + string.Join(", ", occurrences.Select(kv => $"{kv.Key}^{kv.Value}")) + " }}";
}