using System.Collections;
using System.Collections.Immutable;
using System.Diagnostics;
using System.Numerics;
using System.Runtime.CompilerServices;
using ZIPT.IntUtils;
using ZIPT.Strings;
using ZIPT.Strings.Tokens;

namespace ZIPT.MiscUtils;

public static class CollectionExtension {

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static void Pop<T>(this List<T> list, int cnt) =>
        list.RemoveRange(list.Count - cnt, cnt);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static T Pop<T>(this List<T> list) {
        T res = list[^1];
        list.RemoveAt(list.Count - 1);
        return res;
    }

    public static bool IsEmpty<T>(this IReadOnlyCollection<T> list) =>
        list.Count == 0;

    public static bool IsNonEmpty<T>(this IReadOnlyCollection<T> list) =>
        list.Count != 0;

    public static bool IsWord(this IList<StrToken> list) =>
        list.All(o => o is CharToken);

    public static NList<T> ToNList<T>(this IEnumerable<T> list) where T : IComparable<T> => new(list);
    public static NList<T> ToNList<T>(this NList<T> list) where T : IComparable<T> => new(list);

    public static void AddRange<T>(this HashSet<T> set, IEnumerable<T> items) {
        foreach (var elem in items) {
            set.Add(elem);
        }
    }

    public static S GetOrEmpty<T, S>(this Dictionary<T, S> dict, T val) where T : notnull where S : new() {
        if (dict.TryGetValue(val, out var res))
            return res;
        dict.Add(val, res = new S());
        return res;
    }

    public static bool EqualContent<T, S>(this IReadOnlyDictionary<T, S> dict1, IReadOnlyDictionary<T, S> dict2)
        where T : notnull where S : IEquatable<S> {
        if (dict1.Count != dict2.Count)
            return false;

        foreach (var kvp in dict1) {
            if (!dict2.TryGetValue(kvp.Key, out var value) || !kvp.Value.Equals(value)) {
                return false;
            }
        }
        return true;
    }

    public static void Add<K, T>(this Dictionary<K, PDD<T>> dict, K key, PDD<T> val) 
        where K : notnull where T : struct, INumberBase<T>, IComparable<T> {

        if (val.IsZero) 
            return;
        if (dict.TryGetValue(key, out var prev))
            dict[key] = val.Add(prev);
        else
            ((IDictionary<K, PDD<T>>)dict).Add(key, val);
    }

    public static ImmutableDictionary<K, uint> Add<K>(this ImmutableDictionary<K, uint> dict, K key, uint val) where K : notnull {
        if (val == 0) 
            return dict;
        if (dict.ContainsKey(key))
            return dict.Add(key, val);
        return dict.SetItem(key, val);
    }

    public static ImmutableDictionary<K, uint> Sub<K>(this ImmutableDictionary<K, uint> dict, K key, uint val) where K : notnull {
        if (val == 0) 
            return dict;
        Debug.Assert(dict.ContainsKey(key));
        Debug.Assert(dict[key] >= val);
        uint prev = dict[key];
        if (prev == val)
            return dict.Remove(key);
        return dict.SetItem(key, prev - val);
    }

    public static void Dec<T>(this Dictionary<T, uint> dict, T val) where T : notnull {
        if (!dict.TryGetValue(val, out var cnt)) {
            Debug.Assert(false);
            return;
        }
        if (cnt == 1)
            dict.Remove(val);
        else
            dict[val] = cnt - 1;
    }

    public static void Inc<T>(this Dictionary<T, uint> dict, T val) where T : notnull {
        if (!dict.TryGetValue(val, out var cnt)) 
            dict.Add(val, 1);
        else
            dict[val] = cnt + 1;
    }

    public static void Inc<T>(this Dictionary<T, uint> dict1, IReadOnlyDictionary<T, uint> dict2) where T : notnull {
        foreach (var kvp in dict2) {
            if (dict1.TryGetValue(kvp.Key, out var cnt))
                dict1[kvp.Key] = cnt + kvp.Value;
            else
                dict1.Add(kvp.Key, kvp.Value);
            Debug.Assert(dict1[kvp.Key] > 0);
        }
    }

    public static IEnumerable<List<T>> CartesianProduct<T>(this IList<IList<T>> cases) {
        List<T> result = [];
        var cartesianEnumerator = cases.Select(o =>
        {
            var ret = o.GetEnumerator();
            Log.Verify(ret.MoveNext());
            result.Add(ret.Current);
            return ret;
        }).ToList();

        while (true) {

            for (int i = cartesianEnumerator.Count; i < cases.Count; i++) {
                cartesianEnumerator.Add(cases[i].GetEnumerator());
                Log.Verify(cartesianEnumerator[^1].MoveNext());
                result.Add(cartesianEnumerator[^1].Current);
            }
            yield return result;

            while (!cartesianEnumerator.IsEmpty() && !cartesianEnumerator[^1].MoveNext()) {
                cartesianEnumerator.Pop().Dispose();
            }
            if (cartesianEnumerator.Count == 0)
                yield break;
            result = [];
            result.AddRange(cartesianEnumerator.Select(s => s.Current));
        }
    }

    public static IEnumerable<List<T>> Subsets<T>(this List<T> set) {

        if (set.Count >= 31)
            throw new NotSupportedException("Too many elements in the set");
        if (set.Count == 0) {
            yield return [];
            yield break;
        }
        BitArray bits = new(set.Count);
        uint cnt = 1u << set.Count;
        List<T> result = [];
        yield return result;
        for (uint i = 0; i < cnt - 1; i++) {
            for (int j = bits.Count; j > 0; j--) {
                if (bits[j - 1]) {
                    bits[j - 1] = false;
                    result.Pop();
                }
                else {
                    bits[j - 1] = true;
                    result.Add(set[j - 1]);
                    break;
                }
            }
            yield return result;
        }
    }

    public static T[] EmptyOrUnit<T>(T? elem) where T : struct => elem is null ? Array.Empty<T>() : [elem.Value];
    public static T[] EmptyOrUnit<T>(T? elem) => elem is null ? Array.Empty<T>() : [elem];
}