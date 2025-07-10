using Microsoft.Z3;
using System;
using System.Diagnostics;
using System.Runtime.CompilerServices;
using ZIPT.MiscUtils;
using ZIPT.Tokens;

namespace ZIPT.Constraints;

public class SharedStr : IStr {

    readonly Environment env;
    public readonly uint Id;
    // refIdx % 2 == 0: reference to tokens
    // refIdx % 2 == 1: reference to other slice
    readonly IReadOnlyList<uint> refIndexes;

    // this is NOT necessarily refIndexes.Count
    // TODO: Maybe use a cumulative sum of sub-lengths to use binary search for index access?
    public uint Length { get; }
    public bool Ground { get; }
    public bool Word { get; }

    public IReadOnlyDictionary<NamedStrToken, uint> ContainedVariables { get; }

    public SharedStr(Environment env, uint id, IReadOnlyList<uint> refIndexes, uint length, bool ground, bool word, IReadOnlyDictionary<NamedStrToken, uint> containedVariables) {
        Debug.Assert(!word || ground);
        this.env = env;
        Id = id;
        this.refIndexes = refIndexes;
        Length = length;
        Ground = ground;
        Word = word;
        ContainedVariables = containedVariables;
        Debug.Assert(GetTokens().Count() == Length);
        Debug.Assert(Ground == containedVariables.IsEmpty());
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
    SharedStr DeRefSlice(uint refIdx) {
        Debug.Assert(refIdx % 2 == 1);
        return env.RefSlices[(int)(refIdx / 2)];
    }

    public StrToken this[int index] => PeekFirst(index);

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
                SharedStr otherSlice = env.RefSlices[(int)(refIdx / 2)];
                for (int i = otherSlice.refIndexes.Count; i > 0; i--) {
                    stack.Push(otherSlice.refIndexes[i]);
                }
            }
        }
    }

    public IEnumerable<StrToken> GetTokensRev() {
        Stack<uint> stack = [];
        foreach (var i in refIndexes) {
            stack.Push(i);
        }
        while (stack.Count > 0) {
            uint refIdx = stack.Pop();
            if (refIdx % 2 == 0)
                // Reference to a token
                yield return env.BaseSlices[(int)(refIdx / 2)];
            else {
                // Reference to another slice
                foreach (var i in env.RefSlices[(int)(refIdx / 2)].refIndexes) {
                    stack.Push(i);
                }
            }
        }
    }

    public StrToken Peek(bool dir) => dir
        ? PeekFirst()
        : PeekLast();

    public StrToken Peek(bool dir, int idx) => dir
        ? PeekFirst(idx)
        : PeekLast(idx);

    public StrToken PeekFirst() {
        Debug.Assert(refIndexes.Count > 0);
        uint refIdx = refIndexes[0];
        while (refIdx % 2 == 0) {
            refIdx = DeRefSlice(refIdx).refIndexes[0];
        }
        return DeRefToken(refIdx);
    }

    public StrToken PeekLast() {
        Debug.Assert(refIndexes.Count > 0);
        uint refIdx = refIndexes[^1];
        while (refIdx % 2 == 0) {
            refIdx = DeRefSlice(refIdx).refIndexes[^1];
        }
        return DeRefToken(refIdx);
    }

    public StrToken PeekFirst(int index) {
        if (index < 0 || index >= Length)
            throw new ArgumentOutOfRangeException(nameof(index), "Index out of range");
        SharedStr currentSlice = this;
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
                SharedStr otherSlice = DeRefSlice(refIdx);
                if (c < otherSlice.Length) {
                    currentSlice = otherSlice;
                    break;
                }
                c -= (int)otherSlice.Length;
            }
        }
    }

    public StrToken PeekLast(int index) {
        if (index < 0 || index >= Length)
            throw new ArgumentOutOfRangeException(nameof(index), "Index out of range");
        SharedStr currentSlice = this;
        int c = index;

        while (true) {
            Debug.Assert(c >= 0);
            for (var i = currentSlice.refIndexes.Count; i > 0; i--) {
                var refIdx = currentSlice.refIndexes[i - 1];
                if (refIdx % 2 == 0) {
                    if (index == 0)
                        return DeRefToken(refIdx);
                    c--;
                    continue;
                }
                SharedStr otherSlice = DeRefSlice(refIdx);
                if (c < otherSlice.Length) {
                    currentSlice = otherSlice;
                    break;
                }
                c -= (int)otherSlice.Length;
            }
        }
    }

    public IStr Drop(uint left, uint right) {
        if (left + right > Length)
            return env.MkEmptySharedStr();
     
        List<int> newIndices = new(refIndexes.Count);
        Stack<(uint id, int localPos)> toUnwind = [];
        toUnwind.Push((Id, -1));
        while (left > 0) {
            (uint id, int localPos) current = toUnwind.Peek();
            Debug.Assert(current.id % 2 == 1);
            var indices = env.RefSlices[(int)current.id].refIndexes;
            for (int i = 0; i < indices.Count && left > 0; i++) {
                uint refIdx = indices[i];
                if (refIdx % 2 == 0) {
                    left--;
                }
                else {
                    // Reference to another slice
                    SharedStr otherSlice = DeRefSlice(refIdx);
                    if (left >= otherSlice.Length) {
                        left -= otherSlice.Length;
                        continue;
                    }
                    toUnwind.Push((refIdx, i));
                    break;
                }
            }
        }
        while (toUnwind.IsNonEmpty()) {
            var current = toUnwind.Pop();

        }
    }

    public SharedStr ApplySubst(NamedStrToken v, SharedStr str) {
        if (!ContainedVariables.ContainsKey(v))
            return this;
        Stack<uint> todo = [];
        List<uint> newRefIdx = new(refIndexes.Count);
        bool isWord = true;
        bool isGround = true;
        bool isWordMod = str.Word;
        bool isGroundMod = str.Ground;
        for (int i = refIndexes.Count; i > 0; i--) {
            todo.Push(refIndexes[i]);
        }
        while (todo.Count > 0) {
            uint refIdx = todo.Pop();
            if (refIdx % 2 == 0) {
                StrToken t = DeRefToken(refIdx);
                if (t.Equals(v)) {
                    newRefIdx.Add(str.Id);
                    isWord &= isWordMod;
                    isGround &= isGroundMod;
                }
                else {
                    newRefIdx.Add(refIdx);
                    isWord &= t is CharToken;
                    isGroundMod &= t is not NamedStrToken;
                }
                continue;
            }
            SharedStr otherSlice = DeRefSlice(refIdx);
            if (!otherSlice.ContainedVariables.ContainsKey(v)) {
                newRefIdx.Add(refIdx);
                isWord &= otherSlice.Word;
                isGround &= otherSlice.Ground;
                continue;
            }
            for (int i = otherSlice.refIndexes.Count; i > 0; i--) {
                todo.Push(otherSlice.refIndexes[i]);
            }
        }
        IReadOnlyDictionary<NamedStrToken, uint> newContainedVars;
        if (str.ContainedVariables.Count == 1 && str.ContainedVariables.ContainsKey(v))
            newContainedVars = ContainedVariables;
        else {
            var dict = new Dictionary<NamedStrToken, uint>(ContainedVariables);
            dict.Dec(v);
            dict.Inc(str.ContainedVariables);
            newContainedVars = dict;
        }
        var slice = new SharedStr(env, (uint)env.RefSlices.Count, newRefIdx, Length, isGround, isWord, newContainedVars);
        env.RefSlices.Add(slice);
        return slice;
    }

    public override int GetHashCode() =>
        GetTokens().Aggregate(387815837, (hash, token) => hash * 941706509 + token.GetHashCode());

    public override bool Equals(object? obj) =>
        obj is IStr slice && ((IStr)this).Equals(slice);
}