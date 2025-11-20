using Microsoft.Z3;
using System;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using ZIPT.IntUtils;
using ZIPT.Strings.Tokens;

namespace ZIPT.MiscUtils;

/*public class MinTerms {

    // Mutually disjoint character sets
    public List<CharacterSet> Sets { get; } = [];

    public uint CharacterCount => (uint)Sets.Sum(o => o.CharacterCount);
    public bool IsUnit => Sets is [{ IsUnit: true }];
    public CharToken First => Sets[0].First;

    public MinTerms() { }

    public MinTerms(CharToken c) =>
        Sets.Add(new CharacterSet(new CharacterRange(c.Value)));

    public MinTerms(CharacterSet set) => 
        Sets.Add(set);

    public MinTerms(List<CharacterSet> sets) {
        Debug.Assert(sets.Count == 0 || sets.SkipLast(1).Zip(sets.Skip(1)).All(o => o.First.IsDisjoint(o.Second)));
        Sets = sets;
    }

    public MinTerms Complement() {
        throw new NotImplementedException();
    }

    // TODO: optimize!!!
    public bool Contains(CharacterSet set) {
        foreach (var s in Sets) {
            if (s.IsDisjoint(set))
                continue;
            // set is a subset of this
            Debug.Assert(set.IntersectWith(s).Equals(set));
            return true;
        }
        return false;
    }

    public bool Contains(CharToken c) => 
        Sets.Any(s => s.Contains(c));

    public MinTerms Merge(MinTerms set) {
        // Formally, it is that: https://en.wikipedia.org/wiki/Partition_of_a_set; intersection/meet of a set partition
        // TODO: optimize!!!
        List<CharacterSet> result = set.Sets;
        foreach (var e1 in Sets) {
            List<CharacterSet> s = result;
            result = [];
            foreach (var e2 in s) {
                CharacterSet inter = e1.IntersectWith(e2);
                if (!inter.IsEmpty) 
                    result.Add(inter);
                CharacterSet onlyInE1 = e1.IntersectWith(e2.Complement());
                if (!onlyInE1.IsEmpty)
                    result.Add(onlyInE1);
                CharacterSet onlyInE2 = e2.IntersectWith(e1.Complement());
                if (!onlyInE2.IsEmpty)
                    result.Add(onlyInE2);
            }
        }
        return new MinTerms(result);
    }

    public override string ToString() =>
        "{" + string.Join(";", Sets) + "}";
}*/

// It is a sorted list of tuples (char1, char2, id) representing that [char1, char-2] (inclusive bounds; we do not need the empty set!) belongs to set at id
// This is list sorted by char1 and the interval are disjoint
// this is way easier to merge than sets of CharacterSet
public class MinTerms {

    public List<(uint char1, uint char2, uint id)> Intervals { get; } = [];

    public uint SetCount { get; private set; }

    public uint CharacterCount => (uint)Intervals.Sum(o => o.char2 - o.char1 + 1);
    public bool IsUnit => Intervals.Count == 1 && Intervals[0].char1 == Intervals[0].char2;
    public CharToken First => new(Intervals[0].char1);

    public MinTerms() { }

    public MinTerms(CharToken c) {
        Intervals.Add((c.Value, c.Value, 0));
        SetCount++;
    }

    public MinTerms(CharacterSet set) {
        foreach (var range in set.Ranges) {
            Debug.Assert(range.From < range.To);
            Intervals.Add((range.From, range.To - 1, 0));
        }
        SetCount = 1;
    }

    public MinTerms(IReadOnlyList<CharacterSet> sets) {
        Debug.Assert(sets.Count == 0 || sets.SkipLast(1).Zip(sets.Skip(1)).All(o => o.First.IsDisjoint(o.Second)));
        if (sets.Count == 0)
            return;
        uint[] ids = new uint[sets.Count];
        int[] pos = new int[sets.Count];
        while (true) {
            var minChar = uint.MaxValue;
            var minIdx = -1;
            CharacterRange range;
            for (int i = 0; i < sets.Count; i++) {
                if (pos[i] >= sets[i].Ranges.Count)
                    continue;
                range = sets[i].Ranges[pos[i]];
                if (range.From < minChar) {
                    minChar = range.From;
                    minIdx = i;
                }
            }
            if (minIdx == -1)
                break;
            range = sets[minIdx].Ranges[pos[minIdx]];
            if (ids[minIdx] == 0)
                ids[minIdx] = ++SetCount;
            Intervals.Add((range.From, range.To - 1, ids[minIdx] - 1));
            pos[minIdx]++;
        }
        Debug.Assert(Intervals.IsEmpty() ||
                     Intervals.SkipLast(1).Zip(Intervals.Skip(1)).All(o => o.First.char2 < o.Second.char1));
    }

    public MinTerms(params CharacterSet[] sets) : this((IReadOnlyList<CharacterSet>)sets) { }

    // Adds all the intervals that are missing to have the full range
    public MinTerms Complete() {
        if (Intervals.Count == 0)
            return new MinTerms(CharacterSet.Full);
        MinTerms ret = new() {
            SetCount = SetCount,
        };
        int i = 0;
        uint start = 0;
        uint prevId = 0;
        uint newId = 0;

        while (true) {
            for (; i < Intervals.Count && Intervals[i].char1 == start; i++) {
                ret.Intervals.Add(Intervals[i].id < newId - 1
                    ? Intervals[i]
                    : (Intervals[i].char1, Intervals[i].char2, Intervals[i].id + 1));
                start = Intervals[i].char2 + 1;
                prevId = uint.Max(prevId, Intervals[i].id + 1);
            }
            if (i >= Intervals.Count) {
                if (start < CharacterSet.MaxChar) {
                    if (newId == 0) {
                        newId = prevId + 1;
                        ret.SetCount++;
                    }
                    ret.Intervals.Add((start, CharacterSet.MaxChar, newId - 1));
                }
                Debug.Assert(ret.Intervals.IsEmpty() ||
                             ret.Intervals.SkipLast(1).Zip(ret.Intervals.Skip(1)).All(o => o.First.char2 < o.Second.char1));
                Debug.Assert(ret.Intervals.All(o => o.char1 <= o.char2));
                return ret;
            }
            if (newId == 0) {
                newId = prevId + 1;
                ret.SetCount++;
            }
            ret.Intervals.Add((start, Intervals[i].char1 - 1, newId - 1));
            ret.Intervals.Add(Intervals[i].id < newId - 1
                ? Intervals[i]
                : (Intervals[i].char1, Intervals[i].char2, Intervals[i].id + 1));
            prevId = uint.Max(prevId, Intervals[i].id + 1);
            start = Intervals[i++].char2 + 1;
        }
    }

    public MinTerms Complement() {
        if (Intervals.Count == 0)
            return new MinTerms(CharacterSet.Full);
        MinTerms ret = new();
        int i = 0;
        uint start = 0;

        while (true) {
            for (; i < Intervals.Count && Intervals[i].char1 == start; i++) {
                start = Intervals[i].char2;
            }
            if (i >= Intervals.Count) {
                if (start != CharacterSet.MaxChar)
                    ret.Intervals.Add((start, CharacterSet.MaxChar - 1, 0));
                return ret;
            }
            ret.Intervals.Add((start, Intervals[i].char2 - 1, 0));
            start = Intervals[i++].char2 + 1;
        }
    }

    // TODO: optimize!!!
    public bool Contains(CharacterSet set) {
        // Use binary search to find each range of set in Intervals
        // TODO: Check!
        int low = 0;
        foreach (var range in set.Ranges) {
            int high = Intervals.Count - 1;
            while (low <= high) {
                int mid = (low + high) / 2;
                if (Intervals[mid].char1 > range.To)
                    high = mid - 1;
                else if (Intervals[mid].char2 < range.From)
                    low = mid + 1;
                else
                    break;
            }
            if (low > high)
                return false;
            Debug.Assert(low == high);
            if (Intervals[low].char2 >= range.To)
                return false;

        }
        return true;
    }

    public bool Contains(CharToken c) {
        // binary search
        int low = 0;
        int high = Intervals.Count - 1;
        while (low <= high) {
            int mid = (low + high) / 2;
            if (Intervals[mid].char1 > c.Value)
                high = mid - 1;
            else if (Intervals[mid].char2 < c.Value)
                low = mid + 1;
            else
                return true;
        }
        return false;
    }

    public MinTerms Merge(MinTerms set, bool dropDiff = false) {
        // Formally, it is that: https://en.wikipedia.org/wiki/Partition_of_a_set; intersection/meet of a set partition
        // TODO: optimize!!!
        // Sweep line approach for computing the finest refinement
        if (set.Intervals.Count == 0)
            return this;
        if (Intervals.Count == 0)
            return set;

        MinTerms ret = new();
        int i = 0, j = 0;
        Dictionary<(uint id1, uint id2), uint> idMap = []; // TODO: Maybe a 2d array?
        uint min1 = Intervals[0].char1;
        uint min2 = set.Intervals[0].char1;
        uint id;

        while (i < Intervals.Count && j < set.Intervals.Count) {
            if (min1 == uint.MaxValue)
                min1 = Intervals[i].char1;
            if (min2 == uint.MaxValue)
                min2 = set.Intervals[j].char1;

            if (min1 < min2) {
                var a = Intervals[i];
                if (min2 > a.char2) {
                    // no intersection
                    if (!dropDiff) {
                        if (!idMap.TryGetValue((Intervals[i].id, uint.MaxValue), out id))
                            idMap.Add((Intervals[i].id, uint.MaxValue), id = ret.SetCount++);
                        ret.Intervals.Add((min1, a.char2, id));
                    }
                    i++;
                    min1 = uint.MaxValue;
                    continue;
                }
                // it intersects partially
                if (!dropDiff) {
                    if (!idMap.TryGetValue((Intervals[i].id, uint.MaxValue), out id))
                        idMap.Add((Intervals[i].id, uint.MaxValue), id = ret.SetCount++);
                    ret.Intervals.Add((min1, min2 - 1, id));
                }
                // proceed to "min1 == min2 case"
                min1 = min2;
            }
            else if (min1 > min2) {
                var b = set.Intervals[j];
                if (min1 > b.char2) {
                    // no intersection
                    if (!dropDiff) {
                        if (!idMap.TryGetValue((uint.MaxValue, set.Intervals[j].id), out id))
                            idMap.Add((uint.MaxValue, set.Intervals[j].id), id = ret.SetCount++);
                        ret.Intervals.Add((min2, b.char2, id));
                    }
                    j++;
                    min2 = uint.MaxValue;
                    continue;
                }
                // it intersects partially
                if (!dropDiff) {
                    if (!idMap.TryGetValue((uint.MaxValue, set.Intervals[j].id), out id))
                        idMap.Add((uint.MaxValue, set.Intervals[j].id), id = ret.SetCount++);
                    ret.Intervals.Add((min2, min1 - 1, id));
                }
                // proceed to "min1 == min2 case"
                min2 = min1;
            }
            if (!idMap.TryGetValue((Intervals[i].id, set.Intervals[j].id), out id))
                idMap.Add((Intervals[i].id, set.Intervals[j].id), id = ret.SetCount++);
            if (Intervals[i].char2 < set.Intervals[j].char2) {
                // interval i ends first
                ret.Intervals.Add((min1, Intervals[i].char2, id));
                min2 = Intervals[i].char2 + 1;
                min1 = uint.MaxValue;
                i++;
            }
            else if (Intervals[i].char2 > set.Intervals[j].char2) {
                // interval j ends first
                ret.Intervals.Add((min2, set.Intervals[j].char2, id));
                min1 = set.Intervals[j].char2 + 1;
                min2 = uint.MaxValue;
                j++;
            }
            else {
                // both end together
                ret.Intervals.Add((min1, Intervals[i].char2, id));
                min1 = uint.MaxValue;
                min2 = uint.MaxValue;
                i++;
                j++;
            }
        }

        if (i < Intervals.Count) {
            var a = Intervals[i];
            if (!idMap.TryGetValue((Intervals[i].id, uint.MaxValue), out id))
                idMap.Add((Intervals[i].id, uint.MaxValue), id = ret.SetCount++);
            ret.Intervals.Add((min1 == uint.MaxValue ? a.char1 : min1, a.char2, id));
            while (++i < Intervals.Count) {
                a = Intervals[i];
                if (!idMap.TryGetValue((Intervals[i].id, uint.MaxValue), out id))
                    idMap.Add((Intervals[i].id, uint.MaxValue), id = ret.SetCount++);
                ret.Intervals.Add((a.char1, a.char2, id));
            }
        }
        else if (j < set.Intervals.Count) {
            var b = set.Intervals[j];
            if (!idMap.TryGetValue((uint.MaxValue, set.Intervals[j].id), out id))
                idMap.Add((uint.MaxValue, set.Intervals[j].id), id = ret.SetCount++);
            ret.Intervals.Add((min2 == uint.MaxValue ? b.char1 : min2, b.char2, id));
            while (++j < set.Intervals.Count) {
                b = set.Intervals[j];
                if (!idMap.TryGetValue((uint.MaxValue, set.Intervals[j].id), out id))
                    idMap.Add((uint.MaxValue, set.Intervals[j].id), id = ret.SetCount++);
                ret.Intervals.Add((b.char1, b.char2, id));
            }
        }
        Debug.Assert(ret.Intervals.IsEmpty() || 
                     ret.Intervals.SkipLast(1).Zip(ret.Intervals.Skip(1)).All(o => o.First.char2 < o.Second.char1));
        Debug.Assert(ret.Intervals.All(o => o.char1 <= o.char2));
        return ret;
    }

    [Pure]
    public List<CharacterSet> ToCharacterSets() {
        Debug.Assert(Intervals.IsEmpty() ||
                     Intervals.SkipLast(1).Zip(Intervals.Skip(1)).All(o => o.First.char2 < o.Second.char1));
        List<List<CharacterRange>> rangesList = [];
        foreach (var range in Intervals) {
            if (range.id >= rangesList.Count) {
                Debug.Assert(range.id == rangesList.Count);
                List<CharacterRange> ranges = [new(range.char1, range.char2 + 1)];
                rangesList.Add(ranges);
                continue;
            }
            rangesList[(int)range.id].Add(new CharacterRange(range.char1, range.char2 + 1));
        }
        List<CharacterSet> set = new List<CharacterSet>(rangesList.Count);
        foreach (var range in rangesList) {
            set.Add(CharacterSet.TakeFromList(range));
        }
        return set;
    }

    public override string ToString() {
        var sets = ToCharacterSets();
        return "{" + string.Join(";", sets) + "}";
    }
}