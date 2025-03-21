using System.Collections;
using System.Diagnostics;

namespace StringBreaker.MiscUtils;

public static class CollectionExtension {

    public static void Pop<T>(this List<T> list, int cnt) =>
        list.RemoveRange(list.Count - cnt, cnt);

    public static T Pop<T>(this List<T> list) {
        T res = list[^1];
        list.RemoveAt(list.Count - 1);
        return res;
    }

    public static bool IsEmpty<T>(this IReadOnlyCollection<T> list) =>
        list.Count == 0;

    public static bool IsNonEmpty<T>(this IReadOnlyCollection<T> list) =>
        list.Count != 0;

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

    public static IEnumerable<List<T>> CartesianProduct<T>(this IList<IList<T>> cases) {
        List<T> result = [];
        var cartesianEnumerator = cases.Select(o =>
        {
            var ret = o.GetEnumerator();
            bool success = ret.MoveNext();
            Debug.Assert(success); // we checked this before with the return
            result.Add(ret.Current);
            return ret;
        }).ToList();

        while (true) {

            for (int i = cartesianEnumerator.Count; i < cases.Count; i++) {
                cartesianEnumerator.Add(cases[i].GetEnumerator());
                bool success = cartesianEnumerator[^1].MoveNext();
                Debug.Assert(success); // again, it is not empty
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

}