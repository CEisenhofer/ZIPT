using System.Diagnostics;
using System.Diagnostics.CodeAnalysis;
using System.Runtime.CompilerServices;
using System.Xml.Linq;
using ZIPT.Constraints;
using ZIPT.MiscUtils;
using ZIPT.Strings.Tokens;

namespace ZIPT.Strings.Chunks;

public sealed class TupleStr : Str, IEquatable<TupleStr> {

    public Str Left { get; }
    public Str Right { get; }

    // Maybe
    HashSet<NamedStrToken>? containedVars;

    TriangleMatrix hashMatrix;
    int hash;

    public readonly Dictionary<uint, Str> DropLeftCache = [];
    public readonly Dictionary<uint, Str> DropRightCache = [];
    public readonly Dictionary<(NamedStrToken, Str), Str> SubstCache = [];
    StrToken[]? seqCache;

    public override uint Length { get; }
    public override uint Level { get; }
    public override bool Balanced => IsBalanced(Left, Right);
    public override bool BalancedTrans => Balanced && Left.BalancedTrans && Right.BalancedTrans;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    [MemberNotNull(nameof(containedVars))]
    void InitContainedVars() {
        if (containedVars is not null)
            return;
        Left.CollectVars(containedVars = []);
        Right.CollectVars(containedVars);
    }

    public override bool ContainsVar(NamedStrToken v) {
        InitContainedVars();
        return containedVars.Contains(v);
    }

    public override void CollectVars(HashSet<NamedStrToken> contained) {
        InitContainedVars();
        foreach (var v in containedVars) {
            contained.Add(v);
        }
    }

    public override void CollectSymbols(NonTermSet nonTermSet, HashSet<CharToken> alphabet) {
        Left.CollectSymbols(nonTermSet, alphabet);
        Right.CollectSymbols(nonTermSet, alphabet);
    }

    public static bool IsBalanced(Str left, Str right) =>
        Math.Abs((int)left.Level - (int)right.Level) <= 1;

    public TupleStr(Str left, Str right) : this(uint.MaxValue, left, right) {
        // temporal chunk
    }

    public TupleStr(uint chunkId, Str left, Str right) : base(chunkId) {
        Left = left;
        Right = right;
        Length = left.Length + right.Length;
        Level = Math.Max(left.Level, right.Level) + 1;
        Ground = left.Ground && right.Ground;
    }

    public override TupleStr Translate(StrManager manager) {
        var left = Left.Translate(manager);
        var right = Right.Translate(manager);
        return (TupleStr)manager.Concat(left, right);
    }

    public override IReadOnlyList<StrToken> Sequence() {
        if (seqCache is not null)
            return seqCache;
        // Not sure if we should cache also children
        var tokens = new StrToken[Length];
        Stack<Str> todo = [];
        Str s = this;
        int i = 0;
        while (true) {
            bool cacheHit = false;
            while (s is TupleStr lts) {
                if (lts.seqCache is not null) {
                    lts.seqCache.CopyTo(tokens, i);
                    i += lts.seqCache.Length;
                    cacheHit = true;
                    break;
                }
                todo.Push(lts.Right);
                s = lts.Left;
            }
            if (!cacheHit) {
                Debug.Assert(s is SingletonStr);
                SingletonStr single = (SingletonStr)s;
                tokens[i++] = single.StrToken;
            }
            if (todo.Count == 0) {
                seqCache = tokens;
                return tokens;
            }
            Debug.Assert(todo.Count > 0);
            s = todo.Pop();
        }
    }

    protected override int CompareToInternal(Str other) {
        var otherTuple = (TupleStr)other;
        int cmp = Left.CompareTo(otherTuple.Left);
        return cmp != 0 ? cmp : Right.CompareTo(otherTuple.Right);
    }

    public override bool Equals(object? obj) =>
        obj is TupleStr other && Equals(other);

    public override bool Equals(Str? other) =>
        other is TupleStr tc && Equals(tc);

    public bool Equals(TupleStr? other) {
        if (other is null)
            return false;
        if (ReferenceEquals(this, other))
            return true;
        Debug.Assert(ChunkId != other.ChunkId);
        if (Length != other.Length)
            return false;
        InitHash();
        other.InitHash();
        if (hash != other.hash)
            return false;
        if (containedVars is not null && other.containedVars is not null) {
            if (containedVars.Count != other.containedVars.Count)
                return false;
            if (!containedVars.SetEquals(other.containedVars))
                return false;
        }
        // now let's do expensive structural comparison
        Stack<Str> toDoLeft = [];
        Stack<Str> toDoRight = [];
        Str left = this;
        Str right = other;
        while (true) {
            // TODO: Actually we can call a subprocedure equality check again if left & right have same length
            // Get next token from left
            while (left is TupleStr ltc && right is TupleStr rtc) {
                int cmp = left.Length.CompareTo(right.Length);
                if (cmp == 0) {
                    if (ReferenceEquals(left, right))
                        goto skip;
                    /*if (!left.Equals(right))
                        return false;*/
                }
                if (cmp > 0) {
                    toDoLeft.Push(ltc.Right);
                    left = ltc.Left;
                }
                else {
                    toDoRight.Push(rtc.Right);
                    right = rtc.Left;
                }
            }
            while (left is TupleStr ltc) {
                toDoLeft.Push(ltc.Right);
                left = ltc.Left;
            }
            Debug.Assert(left is SingletonStr);
            while (right is TupleStr rtc) {
                toDoRight.Push(rtc.Right);
                right = rtc.Left;
            }
            Debug.Assert(right is SingletonStr);
            if (!left.Equals(right))
                return false;

            skip:
            if (toDoLeft.Count == 0)
                break;
            Debug.Assert(toDoRight.Count > 0);
            left = toDoLeft.Pop();
            right = toDoRight.Pop();
        }

        Debug.Assert(toDoLeft.Count == toDoRight.Count);
        return true;
    }

    // the hash needs to be associative but not commutative
    // one idea: polynomial rolling (https://en.wikipedia.org/wiki/Rolling_hash)
    // h(l_1, ..., l_n) = (h(l_1, ..., l_{n-1}) * base + l_n) mod p
    // we could use p = int.MaxValue (2147483647 - it is by coincidence prime and smaller equal than int.MaxValue so perfect :D)
    // but this explodes because of huge multiplications
    // We use a matrix multiplication instead
    void InitHash() {
        if (hash != 0)
            return;
        Debug.Assert(Left is not EmptyStr);
        Debug.Assert(Right is not EmptyStr);
        TriangleMatrix leftMatrix, rightMatrix;
        if (Left is TupleStr ltc) {
            ltc.InitHash();
            leftMatrix = ltc.hashMatrix;
        }
        else
            leftMatrix = new TriangleMatrix(Left);
        if (Right is TupleStr rtc) {
            rtc.InitHash();
            rightMatrix = rtc.hashMatrix;
        }
        else
            rightMatrix = new TriangleMatrix(Right);
        hashMatrix = new TriangleMatrix(leftMatrix, rightMatrix);
        hash = hashMatrix.GetHashCode();
        // hypothetically "hash" could be 0 again, but this is very unlikely and would just affect performance
    }

    public override int GetHashCode() {
        InitHash();
        return hash;
    }

    public override string RawString => $"({Left.RawString}{Right.RawString})";
    public override string GetPlainString(NielsenGraph? graph) => Left.GetPlainString(graph) + Right.GetPlainString(graph); 
}