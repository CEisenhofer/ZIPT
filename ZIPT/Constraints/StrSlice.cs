using System.Diagnostics;
using System.Runtime.CompilerServices;
using System.Text;
using ZIPT.MiscUtils;
using ZIPT.Tokens;

namespace ZIPT.Constraints;

public class StrSlice {

    readonly Environment env;
    public readonly uint Id;
    // refIdx % 2 == 0: reference to tokens
    // refIdx % 2 == 1: reference to other slice
    readonly IReadOnlyList<uint> refIndexes;

    // this is NOT necessarily refIndexes.Count
    // TODO: Maybe use a cumulative sum of sub-lengths to use binary search for index access?
    public readonly uint Length;

    readonly IReadOnlyDictionary<NamedStrToken, uint> containedVariables;

    public StrSlice(Environment env, uint id, IReadOnlyList<uint> refIndexes, uint length, IReadOnlyDictionary<NamedStrToken, uint> containedVariables) {
        this.env = env;
        Id = id;
        this.refIndexes = refIndexes;
        Length = length;
        this.containedVariables = containedVariables;
        Debug.Assert(GetTokens().Count() == Length);
        Debug.Assert(containedVariables.EqualContent(
            GetTokens().OfType<NamedStrToken>().
                GroupBy(o => o).
                ToDictionary(
                    o => o.Key, 
                    o => (uint)o.Count())));
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining | MethodImplOptions.AggressiveOptimization)]
    StrToken DeRefToken(uint refIdx) {
        Debug.Assert(refIdx % 2 == 0);
        return env.BaseSlices[(int)(refIdx / 2)];
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining | MethodImplOptions.AggressiveOptimization)]
    StrSlice DeRefSlice(uint refIdx) {
        Debug.Assert(refIdx % 2 == 1);
        return env.RefSlices[(int)(refIdx / 2)];
    }

    public StrToken this[int index] {
        get {
            if (index < 0 || index >= Length)
                throw new ArgumentOutOfRangeException(nameof(index), "Index out of range");
            StrSlice currentSlice = this;
            int c = index;

            while (true) {
                Debug.Assert(c >= 0);
                foreach (var refIdx in currentSlice.refIndexes) {
                    if (refIdx % 2 == 0) {
                        if (index == 0)
                            return DeRefToken(refIdx);
                        c--;
                        continue;
                    }
                    StrSlice otherSlice = DeRefSlice(refIdx);
                    if (c < otherSlice.Length) {
                        currentSlice = otherSlice;
                        break;
                    }
                    c -= (int)otherSlice.Length;
                }
            }
        }
    }

    public IEnumerable<StrToken> GetTokens() {
        Stack<uint> stack = [];
        for (int i = refIndexes.Count; i > 0; i--) {
            stack.Push(refIndexes[i]);
        }
        while (stack.Count > 0) {
            uint refIdx = stack.Pop();
            if (refIdx % 2 == 0)
                // Reference to a token
                yield return env.BaseSlices[(int)(refIdx / 2)];
            else {
                // Reference to another slice
                StrSlice otherSlice = env.RefSlices[(int)(refIdx / 2)];
                for (int i = otherSlice.refIndexes.Count; i > 0; i--) {
                    stack.Push(otherSlice.refIndexes[i]);
                }
            }
        }
    }

    public StrSliceRef ApplySubst(NamedStrToken v, StrSlice str) {
        if (!containedVariables.ContainsKey(v))
            return new StrSliceRef(this);
        Stack<uint> todo = [];
        List<uint> newRefIdx = new List<uint>(refIndexes.Count);
        for (int i = refIndexes.Count; i > 0; i--) {
            todo.Push(refIndexes[i]);
        }
        while (todo.Count > 0) {
            uint refIdx = todo.Pop();
            if (refIdx % 2 == 0) {
                StrToken t = DeRefToken(refIdx);
                newRefIdx.Add(t.Equals(v) ? str.Id : refIdx);
                continue;
            }
            StrSlice otherSlice = DeRefSlice(refIdx);
            if (!otherSlice.containedVariables.ContainsKey(v)) {
                newRefIdx.Add(refIdx);
                continue;
            }
            for (int i = otherSlice.refIndexes.Count; i > 0; i--) {
                todo.Push(otherSlice.refIndexes[i]);
            }
        }
        IReadOnlyDictionary<NamedStrToken, uint> newContainedVars;
        if (str.containedVariables.Count == 1 && str.containedVariables.ContainsKey(v))
            newContainedVars = containedVariables;
        else {
            var dict = new Dictionary<NamedStrToken, uint>(containedVariables);
            dict.Dec(v);
            dict.Inc(str.containedVariables);
            newContainedVars = dict;
        }
        var slice = new StrSlice(env, (uint)env.RefSlices.Count, newRefIdx, Length, newContainedVars);
        env.RefSlices.Add(slice);
        return new StrSliceRef(slice);
    }

    public override int GetHashCode() => 
        GetTokens().Aggregate(387815837, (hash, token) => hash * 941706509 + token.GetHashCode());

    public override bool Equals(object? obj) => 
        obj is StrSlice slice && Equals(slice);

    public bool Equals(StrSlice? other) {
        if (other is null)
            return false;
        if (Length != other.Length)
            return false;
        using var enumerator = GetTokens().GetEnumerator();
        using var otherEnumerator = other.GetTokens().GetEnumerator();
        while (enumerator.MoveNext() && otherEnumerator.MoveNext()) {
            if (!enumerator.Current.Equals(otherEnumerator.Current))
                return false;
        }
        Debug.Assert(GetHashCode() == other.GetHashCode());
        Debug.Assert(containedVariables.EqualContent(other.containedVariables));
        return true;
    }


    public override string ToString() {
        if (Length == 0)
            return "ε";
        StringBuilder sb = new();
        foreach (StrToken token in GetTokens()) {
            sb.Append(token);
        }
        return sb.ToString();
    }
}