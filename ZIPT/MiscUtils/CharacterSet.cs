using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.Net.Http.Headers;
using ZIPT.Strings.Tokens;

namespace ZIPT.MiscUtils;

// Represents a set of possible characters
// It is stored as a sorted list of character ranges
public class CharacterSet : IEquatable<CharacterSet>, IComparable<CharacterSet> {

    public static uint MinChar => 0;
    public static uint MaxChar => Options.MaxChar;

    // TODO: Maybe it is worth having it a self-balanced tree
    // A sorted list of non-overlapping character intervals
    public List<CharacterRange> Ranges { get; } = [];

    public bool IsEmpty => Ranges.Count == 0;
    public bool IsFull => Ranges.Count == 1 && Ranges.First().IsFull;
    public bool IsUnit => Ranges is [{ IsUnit: true } _];
    public CharToken First => new(Ranges[0].From);

    public uint CharacterCount => (uint)Ranges.Sum(o => o.Length);

    public static CharacterSet Empty => new();
    public static CharacterSet Full => 
        new(new CharacterRange(MinChar, MaxChar + 1));

    public CharacterSet(int capacity) => 
        Ranges = new List<CharacterRange>(capacity);

    public CharacterSet(CharacterRange range) => 
        Ranges.Add(range);

    public CharacterSet(params CharacterRange[] range) {
        Ranges = [..range];
        if (range.Length == 0)
            return;
        Ranges.Sort();

        // eliminate overlapping
        int cpyIdx = 1;
        for (int i = 1; i < Ranges.Count; i++) {
            if (Ranges[i].From <= Ranges[cpyIdx].To) {
                Debug.Assert(Ranges[cpyIdx].To <= Ranges[i].To);
                Ranges[cpyIdx] = new CharacterRange(Ranges[cpyIdx].From, Ranges[i].To);
            } else {
                cpyIdx++;
                Ranges[cpyIdx] = Ranges[i];
            }
        }
        
        Ranges.RemoveRange(cpyIdx + 1, Ranges.Count - (cpyIdx + 1));

        Debug.Assert(Ranges.SkipLast(1).Zip(Ranges.Skip(1)).All(o =>
            o.First.From < o.First.To && o.First.To < o.Second.From));
    }

    CharacterSet(List<CharacterRange> range) {
        Debug.Assert(Ranges.SkipLast(1).Zip(Ranges.Skip(1)).All(o =>
            o.First.From < o.First.To && o.First.To < o.Second.From));
        Ranges = range;
    }

    public static CharacterSet TakeFromList(List<CharacterRange> ranges) => 
        new(ranges);

    public CharacterSet Clone() {
        CharacterSet ret = new(Ranges.Count);
        ret.Ranges.AddRange(ret.Ranges);
        return ret;
    }

    public CharacterSet Complement() =>
        FromComplement(this);

    public static CharacterSet FromComplement(CharacterSet cs) {
        if (cs.IsFull)
            return new CharacterSet();
        if (cs.IsEmpty)
            return Full;

        using var e = cs.Ranges.GetEnumerator();
        Log.Verify(e.MoveNext());
        uint from;
        if (e.Current.From == MinChar) {
            from = e.Current.To;
            if (!e.MoveNext())
                return FromComplement(new CharacterSet(new CharacterRange(e.Current.To, MaxChar + 1)));
        }
        else
            from = MinChar;
        CharacterSet set = new();
        do {
            Debug.Assert(from < e.Current.From);
            set.Ranges.Add(new CharacterRange(from, e.Current.From));
            from = e.Current.To;
        } while (e.MoveNext());
        if (from <= MaxChar)
            set.Ranges.Add(new CharacterRange(from, MaxChar + 1));

        Debug.Assert(set.Ranges.SkipLast(1).Zip(set.Ranges.Skip(1)).All(o =>
            o.First.From < o.First.To && o.First.To < o.Second.From));
        return set;
    }

    // Binary search for c
    public bool Contains(CharToken c) {
        int left = 0;
        int right = Ranges.Count - 1;
        while (left <= right) {
            int mid = left + (right - left) / 2;
            int cmp = Ranges[mid].Find(c.Value);
            switch (cmp) {
                case 0:
                    return true;
                case < 0:
                    left = mid + 1;
                    break;
                default:
                    right = mid - 1;
                    break;
            }
        }
        return false;
    }

    public void Add(uint c) {
        if (Ranges.Count == 0) {
            Ranges.Add(new CharacterRange(c));
            return;
        }
        int left = 0;
        int right = Ranges.Count - 1;
        while (left <= right) {
            int mid = left + (right - left) / 2;
            int cmp = Ranges[mid].Find(c);
            switch (cmp) {
                case 0:
                    return;
                case < 0:
                    right = mid - 1;
                    break;
                default:
                    left = mid + 1;
                    break;
            }
        }
        // left is the insertion point
        CharacterRange newRange = new(c);
        bool mergeLeft = left > 0 && Ranges[left - 1].To == c;
        bool mergeRight = left < Ranges.Count && Ranges[left].From == c + 1;
        if (mergeLeft && mergeRight) {
            CharacterRange lr = Ranges[left - 1];
            CharacterRange rr = Ranges[left];
            Ranges[left - 1] = new CharacterRange(lr.From, rr.To);
            Ranges.RemoveAt(left);
            return;
        }
        if (mergeLeft) {
            CharacterRange lr = Ranges[left - 1];
            Ranges[left - 1] = new CharacterRange(lr.From, lr.To + 1);
            return;
        }
        if (mergeRight) {
            CharacterRange rr = Ranges[left];
            Ranges[left] = new CharacterRange(c, rr.To);
            return;
        }
        Ranges.Insert(left, newRange);
    }
    public void Add(CharacterSet other) {
        if (other.IsEmpty)
            return;
        if (IsEmpty) {
            Ranges.AddRange(other.Ranges);
            return;
        }
        int i = 0;
        int j = 0;
        while (j < other.Ranges.Count) {
            CharacterRange or = other.Ranges[j];
            // Find the position to insert or
            while (i < Ranges.Count && Ranges[i].To < or.From) {
                i++;
            }
            if (i == Ranges.Count) {
                // Just append the rest
                Ranges.AddRange(other.Ranges.Skip(j));
                break;
            }
            if (Ranges[i].From > or.To) {
                // No overlap, just insert
                Ranges.Insert(i, or);
                i++;
                j++;
                continue;
            }
            // There is overlap, we need to merge
            uint newFrom = Math.Min(Ranges[i].From, or.From);
            uint newTo = Math.Max(Ranges[i].To, or.To);
            i++;
            j++;
            // Merge with subsequent ranges in this.Ranges
            while (i < Ranges.Count && Ranges[i].From <= newTo) {
                newTo = Math.Max(newTo, Ranges[i].To);
                i++;
            }
            // Merge with subsequent ranges in other.Ranges
            while (j < other.Ranges.Count && other.Ranges[j].From <= newTo) {
                newTo = Math.Max(newTo, other.Ranges[j].To);
                j++;
            }
            // Replace the merged range
            Ranges.Insert(i - 1, new CharacterRange(newFrom, newTo));
        }

        Debug.Assert(Ranges.SkipLast(1).Zip(Ranges.Skip(1)).All(o =>
            o.First.From < o.First.To && o.First.To < o.Second.From));
    }

    [Pure]
    public CharacterSet IntersectWith(CharacterSet other) {
        // TODO: Make this directly change the datastructure

        CharacterSet result = new();
        int i = 0, j = 0;
        while (i < Ranges.Count && j < other.Ranges.Count) {
            CharacterRange r1 = Ranges[i];
            CharacterRange r2 = other.Ranges[j];
            uint from = Math.Max(r1.From, r2.From);
            uint to = Math.Min(r1.To, r2.To);
            if (from < to) 
                result.Ranges.Add(new CharacterRange(from, to));
            if (r1.To < r2.To)
                i++;
            else
                j++;
        }
        return result;
    }

    public bool IsDisjoint(CharacterSet other) {
        int i = 0, j = 0;
        while (i < Ranges.Count && j < other.Ranges.Count) {
            CharacterRange r1 = Ranges[i];
            CharacterRange r2 = other.Ranges[j];
            if (r1.To <= r2.From)
                i++;
            else if (r2.To <= r1.From)
                j++;
            else
                return false;
        }
        return true;
    }

    public bool IsSubset(CharacterSet other) {
        if (CharacterCount > other.CharacterCount)
            return false;
        var res = other.IntersectWith(this);
        return res.CharacterCount == CharacterCount;
    }

    public CharToken GetSome() {
        Debug.Assert(!IsEmpty);
        Debug.Assert(!Ranges[0].IsEmpty);
        return new CharToken((char)Ranges[0].From);
    }

    public override bool Equals(object? other) =>
        other is CharacterSet set && Equals(set);

    public bool Equals(CharacterSet? other) {
        if (other is null)
            return false;
        if (ReferenceEquals(this, other))
            return true;
        if (Ranges.Count != other.Ranges.Count)
            return false;
        return Ranges.SequenceEqual(other.Ranges);
    }

    public override int GetHashCode() => 
        Ranges.Aggregate(182094083, (h, o) => h + 114822469 * o.GetHashCode());

    public int CompareTo(CharacterSet? other) {
        if (other is null)
            return 1;
        if (ReferenceEquals(this, other))
            return 0;
        int cmp = CharacterCount.CompareTo(other.CharacterCount);
        if (cmp != 0)
            return cmp;
        using var e1 = Ranges.GetEnumerator();
        using var e2 = other.Ranges.GetEnumerator();
        while (e1.MoveNext() && e2.MoveNext()) {
            cmp = e1.Current.CompareTo(e2.Current);
            if (cmp != 0)
                return cmp;
        }
        Debug.Assert(!e1.MoveNext() && !e2.MoveNext());
        return 0;
    }

    public override string ToString() => 
        "{ " + string.Join(", ", Ranges) + " }";
}
