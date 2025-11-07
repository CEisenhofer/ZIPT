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

    public void Add(CharacterRange range) {
        Debug.Assert(!range.IsEmpty);
        if (IsEmpty) {
            Ranges.Add(range);
            return;
        }
        int fromLeft = 0, toLeft = 0;
        int fromRight = Ranges.Count - 1, toRight = Ranges.Count - 1;
        bool foundFrom = false, foundTo = false;
        while (fromLeft <= fromRight) {
            int mid = fromLeft + (fromRight - fromLeft) / 2;
            int cmp = Ranges[mid].Find(range.From);
            switch (cmp) {
                case 0:
                    fromLeft = mid;
                    fromRight = mid;
                    foundFrom = true;
                    break;
                case < 0:
                    fromRight = mid - 1;
                    break;
                default:
                    fromLeft = mid + 1;
                    break;
            }
        }
        while (toLeft <= toRight) {
            int mid = toLeft + (toRight - toLeft) / 2;
            int cmp = Ranges[mid].Find(range.To - 1);
            switch (cmp) {
                case 0:
                    toLeft = mid;
                    toRight = mid;
                    foundTo = true;
                    break;
                case < 0:
                    toRight = mid - 1;
                    break;
                default:
                    toLeft = mid + 1;
                    break;
            }
        }
        if (foundFrom && foundTo) {
            // it is already contained
            if (fromLeft == fromRight)
                return;
            Ranges[fromLeft] = new CharacterRange(
                Ranges[fromLeft].From,
                Ranges[toLeft].To);
            Ranges.RemoveRange(fromLeft + 1, toLeft - fromLeft);
            Debug.Assert(Ranges.SkipLast(1).Zip(Ranges.Skip(1)).All(o =>
                o.First.From < o.First.To && o.First.To < o.Second.From));
            return;
        }
        if (foundFrom) {
            Ranges[fromLeft] = new CharacterRange(
                Ranges[fromLeft].From,
                Math.Max(Ranges[fromLeft].To, range.To));
            Ranges.RemoveRange(fromLeft + 1, toLeft - fromLeft);
            Debug.Assert(Ranges.SkipLast(1).Zip(Ranges.Skip(1)).All(o =>
                o.First.From < o.First.To && o.First.To < o.Second.From));
            return;
        }
        if (foundTo) {
            Ranges[toLeft] = new CharacterRange(
                Math.Min(Ranges[toLeft].From, range.From),
                Ranges[toLeft].To);
            Ranges.RemoveRange(fromLeft, toLeft - fromLeft);
            Debug.Assert(Ranges.SkipLast(1).Zip(Ranges.Skip(1)).All(o =>
                o.First.From < o.First.To && o.First.To < o.Second.From));
            return;
        }
        uint newFrom = range.From;
        uint newTo = range.To;
        if (fromLeft > 0 && fromLeft < Ranges.Count && Ranges[fromLeft - 1].To >= range.From) {
            newFrom = Ranges[fromLeft - 1].From;
            fromLeft--;
        }
        if (toRight > 0 && toRight < Ranges.Count && Ranges[toRight].From <= range.To) {
            newTo = Ranges[toRight].To;
            toRight++;
        }
        Ranges.RemoveRange(fromLeft, toRight - fromLeft);
        Ranges.Insert(fromLeft, new CharacterRange(newFrom, newTo));
        Debug.Assert(Ranges.SkipLast(1).Zip(Ranges.Skip(1)).All(o =>
            o.First.From < o.First.To && o.First.To < o.Second.From));
    }

    public void Add(CharacterSet other) {
        // TODO: Optimise?
        foreach (var range in other.Ranges) {
            Add(range);
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

// [From, To)
public readonly struct CharacterRange : IEquatable<CharacterRange>, IComparable<CharacterRange> {
    public readonly uint From;
    public readonly uint To; // excluding!

    public bool IsEmpty => From == To;
    public bool IsFull => From == CharacterSet.MinChar && To == CharacterSet.MaxChar + 1;
    public bool IsUnit => Length == 1;
    public uint Length => To - From;

    public CharacterRange(uint c) : this(c, c + 1) { }

    public CharacterRange(uint from, uint to) {
        From = from;
        To = to;
        Debug.Assert(from <= to);
    }

    public bool Contains(uint c) =>
        c >= From && c <= To;

    public int Find(uint c) =>
        c < From ? -1 : c >= To ? 1 : 0;

    public override bool Equals(object? obj) =>
        obj is CharacterRange other && Equals(other);

    public bool Equals(CharacterRange other) =>
        From == other.From && To == other.To;

    public override int GetHashCode() =>
        HashCode.Combine(From, To);

    static string GetChar(uint c) =>
        c is
            >= 'a' and <= 'z' or
            >= 'A' and <= 'Z' or
            >= '0' and <= '9'
            ? ((char)c).ToString()
            : $"#[{c}]";

    public int CompareTo(CharacterRange other) {
        int cmp = From.CompareTo(other.From);
        return cmp != 0 ? cmp : To.CompareTo(other.To);
    }

    public override string ToString() {
        if (IsEmpty)
            return "[]";
        if (IsFull)
            return "[..]";
        if (From + 1 == To)
            return GetChar(From);
        if (From + 2 == To)
            return $"[{GetChar(From)}{GetChar(To - 1)}]";
        return $"[{GetChar(From)}-{GetChar(To - 1)}]";
    }
}