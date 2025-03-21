using System.Collections;
using System.Diagnostics;
using System.Runtime.CompilerServices;

namespace StringBreaker.MiscUtils;

public class IndexedQueue<T> : ICollection<T>, IReadOnlyCollection<T> where T : notnull {

    T?[] items;
    int CurrentStartPos { get; set; }
    int CurrentLastPos => GetPos(Count - 1);
    int CurrentEndPos => GetPos(Count);

    public int Count { get; private set; }
    public bool IsReadOnly => false;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    int GetPos(int idx) {
        Debug.Assert(idx >= 0);
        return (CurrentStartPos + idx) % items.Length;
    }

    public T this[int idx] {
        get
        {
            Debug.Assert(GetPos(idx) < items.Length);
            return items[GetPos(idx)]!;
        }
        set
        {
            Debug.Assert(GetPos(idx) < items.Length);
            items[GetPos(idx)] = value;
        }
    }

    public bool Remove(T item) {
        int idx;
        if (CurrentEndPos >= CurrentStartPos) {
            idx = Array.IndexOf(items, item, CurrentStartPos, Count);
            if (idx < 0)
                return false;
            for (int i = idx; i < CurrentStartPos + Count; i++) {
                items[i] = items[i + 1];
            }
            Count--;
            return true;
        }
        idx = Array.IndexOf(items, item, CurrentStartPos, items.Length - CurrentStartPos);
        if (idx >= 0) {
            for (int i = idx; i < items.Length - 1; i++) {
                items[i] = items[i + 1];
            }
            items[^1] = items[0];
            for (int i = 0; i < CurrentEndPos; i++) {
                items[i] = items[i + 1];
            }
            Count--;
            return true;
        }
        idx = Array.IndexOf(items, item, 0, CurrentEndPos);
        if (idx < 0)
            return false;
        for (int i = idx; i < CurrentEndPos; i++) {
            items[i] = items[i + 1];
        }
        Count--;
        return true;
    }

    public IndexedQueue() {
        items = new T[1]; // Otw. division by zero!
    }

    public IndexedQueue(ICollection<T> val) {
        if (val.Count == 0) {
            items = new T[1];
            return;
        }
        items = new T[val.Count];
        val.CopyTo(items!, 0);
        Count = val.Count;
    }

    protected IndexedQueue(int capacity) {
        if (capacity <= 0)
            capacity = 1;
        items = new T[capacity];
        Count = 0;
    }

    void EnsureLen(int len) {
        if (len <= items.Length)
            return;

        var newItems = new T[Math.Max(len, 2 * items.Length)];
        if (Count > 0) {
            if (CurrentEndPos > CurrentStartPos) {
                Array.Copy(items, CurrentStartPos,
                    newItems, 0, Count);
            }
            else {
                Array.Copy(items, CurrentStartPos,
                    newItems, 0,
                    items.Length - CurrentStartPos);
                Array.Copy(items, 0,
                    newItems, items.Length - CurrentStartPos,
                    CurrentEndPos);
            }
        }

        items = newItems;
        CurrentStartPos = 0;
    }

    public void Add(T item) => AddLast(item);

    public void AddLast(T item) {
        EnsureLen(Count + 1);
        items[CurrentEndPos] = item;
        Count++;
    }

    public void Add(T item, bool dir) {
        if (dir)
            AddFirst(item);
        else
            AddLast(item);
    }

    public void AddFirst(T item) {
        EnsureLen(Count + 1);
        if (CurrentStartPos == 0)
            CurrentStartPos = items.Length - 1;
        else
            CurrentStartPos--;
        items[CurrentStartPos] = item;
        Count++;
    }

    public void AddRange(ICollection<T> toAdd, bool dir) {
        if (dir)
            AddFirstRange(toAdd);
        else
            AddLastRange(toAdd);
    }

    public void AddLastRange(ICollection<T> toAdd) {
        EnsureLen(Count + toAdd.Count);
        foreach (var item in toAdd) {
            items[CurrentEndPos] = item;
            Count++;
        }
    }

    public void AddFirstRange(ICollection<T> toAdd) {
        EnsureLen(Count + toAdd.Count);
        if (CurrentStartPos < toAdd.Count)
            CurrentStartPos = items.Length - (toAdd.Count - CurrentStartPos);
        else
            CurrentStartPos -= toAdd.Count;
        Debug.Assert(CurrentStartPos >= 0);
        int pos = CurrentStartPos;
        foreach (var item in toAdd) {
            items[pos++] = item;
            if (pos >= items.Length)
                pos = 0;
        }
        Count += toAdd.Count;
    }

    public void Clear() {
        if (CurrentEndPos >= CurrentStartPos) {
            Array.Clear(items, CurrentStartPos, Count);
        }
        else {
            Array.Clear(items, CurrentStartPos, items.Length - CurrentStartPos);
            Array.Clear(items, 0, CurrentEndPos);
        }
        Count = 0;
        CurrentStartPos = 0;
    }

    public bool Contains(T item) => this.Any(o => o.Equals(item));

    public void CopyTo(T[] array, int arrayIndex) {
        if (Count == 0)
            return;
        if (CurrentEndPos > CurrentStartPos) {
            Array.Copy(items, CurrentStartPos, array, arrayIndex, Count);
            return;
        }
        Array.Copy(items, CurrentStartPos, array, arrayIndex, items.Length - CurrentStartPos);
        Array.Copy(items, 0, array, arrayIndex + items.Length - CurrentStartPos, CurrentEndPos);
    }

    public T PeekFirst() {
        Debug.Assert(Count > 0);
        return items[CurrentStartPos]!;
    }

    public T PeekLast() {
        Debug.Assert(Count > 0);
        return items[CurrentLastPos]!;
    }

    public T PopLast() {
        Debug.Assert(Count > 0);
        T item = items[CurrentLastPos]!;
        items[CurrentLastPos] = default!;
        Count--;
        return item;
    }

    public T PopFirst() {
        Debug.Assert(Count > 0);
        T item = items[CurrentStartPos]!;
        items[CurrentStartPos] = default!;
        CurrentStartPos++;
        Count--;
        if (CurrentStartPos >= items.Length)
            CurrentStartPos = 0;
        return item;
    }

    public IEnumerator<T> GetEnumerator() {
        if (Count == 0)
            yield break;
        if (CurrentEndPos > CurrentStartPos) {
            for (int i = CurrentStartPos; i < CurrentStartPos + Count; i++) {
                yield return items[i]!;
            }
            yield break;
        }
        for (int i = CurrentStartPos; i < items.Length; i++) {
            yield return items[i]!;
        }
        for (int i = 0; i < CurrentEndPos; i++) {
            yield return items[i]!;
        }
    }

    IEnumerator IEnumerable.GetEnumerator() => 
        GetEnumerator();
}