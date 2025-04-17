using System.Collections;

namespace StringBreaker.MiscUtils;

public class NList<T> : IEquatable<NList<T>>, IEnumerable<T> where T : IComparable<T> {

    readonly List<T> items;

    public int Count => items.Count;

    public NList() =>
        items = [];

    public NList(int cap) => 
        items = new List<T>(cap);

    public NList(IEnumerable<T> collection) => 
        items = new List<T>(collection);

    public NList(NList<T> collection) => 
        items = new List<T>(collection.items);

    public IEnumerator<T> GetEnumerator() =>
        ((IEnumerable<T>)items).GetEnumerator();

    IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();

    public bool Contains(T item) => 
        items.BinarySearch(item) >= 0;

    // Only apply when normalized
    public bool Remove(T item) {
        int idx = items.BinarySearch(item);
        if (idx < 0)
            return false;
        items.RemoveAt(idx);
        return true;
    }

    public override bool Equals(object? obj) =>
        obj is NList<T> other && Equals(other);

    public bool Equals(NList<T>? other) =>
        other is not null && Count == other.Count && this.SequenceEqual(other);

    public override int GetHashCode() =>
        items.Aggregate(906270727, (current, cnstr) => current * 135719593 + cnstr.GetHashCode());

    public bool Add(T t) {
        int idx = items.BinarySearch(t);
        if (idx >= 0)
            return false;
        items.Insert(~idx, t);
        return true;
    }

    public void Sort() => items.Sort();

    public override string ToString() => string.Join(", ", items);
}