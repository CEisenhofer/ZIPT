using System.Diagnostics;
using ZIPT.MiscUtils;
using ZIPT.Tokens;

namespace ZIPT;

public class Trie {

    public readonly Dictionary<StrToken, Trie> Children = [];

    public uint Id { get; set; } = uint.MaxValue;

    public uint Get(IReadOnlyList<StrToken> tokens) {
        var current = this;
        foreach (StrToken t in tokens) {
            if (!current.Children.TryGetValue(t, out var child))
                return uint.MaxValue;
            current = child;
        }
        return current.Id;
    }

    public void Add(IReadOnlyList<StrToken> tokens, uint id) {
        var current = this;
        int i = 0;
        for (; i < tokens.Count; i++) {
            var t = tokens[i];
            if (!current.Children.TryGetValue(t, out var child))
                break;
            current = child;
        }
        for (; i < tokens.Count; i++) {
            var t = tokens[i];
            Trie child = new Trie();
            current.Children.Add(t, child);
            current = child;
        }
        Debug.Assert(current.Id == uint.MaxValue);
        current.Id = id;
    }

    public List<List<StrToken>> EnumerateAllStrings() {
        // Just for statistics
        List<StrToken> currentPath = [];
        List<List<StrToken>> result = [];
        Stack<Dictionary<StrToken, Trie>.Enumerator> enumerator = [];
        enumerator.Push(Children.GetEnumerator());
        while (enumerator.IsNonEmpty()) {
            var e = enumerator.Peek();
            if (!e.MoveNext()) {
                enumerator.Pop().Dispose();
                if (currentPath.IsNonEmpty())
                    currentPath.Pop();
                continue;
            }
            var kvp = e.Current;
            currentPath.Add(kvp.Key);
            if (kvp.Value.Id != uint.MaxValue) 
                result.Add([..currentPath]);

            if (kvp.Value.Children.IsNonEmpty())
                enumerator.Push(kvp.Value.Children.GetEnumerator());
        }
        Debug.Assert(currentPath.IsEmpty());
        return result;
    }
}