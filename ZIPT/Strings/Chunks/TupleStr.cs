using System.Diagnostics;
using System.Diagnostics.CodeAnalysis;
using System.Runtime.CompilerServices;
using ZIPT.Constraints;
using ZIPT.MiscUtils;
using ZIPT.Strings.Tokens;
using ZIPT.Strings.Tokens.RegexTokens;

namespace ZIPT.Strings.Chunks;

public sealed class TupleStr : Str, IEquatable<TupleStr> {

    public Str Left { get; }
    public Str Right { get; }

    // Maybe
    HashSet<NamedStrToken>? containedVars;
    HashSet<SymCharToken>? containedSChars;
    MinTerms? firstChars;
    MinTerms? lastChars;

    TriangleMatrix hashMatrix;
    int hash;

    public Dictionary<uint, Str>? DropLeftCache;
    public Dictionary<uint, Str>? DropRightCache;
    public Dictionary<(NamedStrToken, Str), Str>? SubstCache;
    public Dictionary<(SymCharToken, UnitToken), Str>? SubstCharCache;
    public Str? SimplifyCache;
    public StrToken[]? ListCache;
    public uint ListCacheFrom;
    public uint ListCacheTo; // from where to where in the list cache [C# does not allow a span here :/]

    public override uint Length { get; }
    public override uint Level { get; }
    public override bool Balanced => IsBalanced(Left, Right);
    public override bool BalancedTrans => Balanced && Left.BalancedTrans && Right.BalancedTrans;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    [MemberNotNull(nameof(containedVars))]
    void InitContainedVars() {
        if (containedVars is not null) {
            Stats.CachedStringVariableContains++;
            return;
        }
        Left.CollectVars(containedVars = []);
        Right.CollectVars(containedVars);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    [MemberNotNull(nameof(containedSChars))]
    void InitContainedSChars() {
        if (containedSChars is not null) {
            Stats.CachedStringVariableContains++;
            return;
        }
        Left.CollectSChars(containedSChars = []);
        Right.CollectSChars(containedSChars);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    [MemberNotNull(nameof(firstChars))]
    void InitFirstCandidates() {
        if (firstChars is not null) {
            Stats.CachedFirstChars++;
            return;
        }
        firstChars = Left.FirstMinTerms();
        if (Left.Nullable)
            firstChars = firstChars.Merge(Right.FirstMinTerms());
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    [MemberNotNull(nameof(lastChars))]
    void InitLastCandidates() {
        if (lastChars is not null) {
            Stats.CachedLastChars++;
            return;
        }
        lastChars = Right.LastMinTerms();
        if (Right.Nullable)
            lastChars = lastChars.Merge(Left.LastMinTerms());
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

    public override bool ContainsSChar(SymCharToken v) {
        InitContainedSChars();
        return containedSChars.Contains(v);
    }

    public override void CollectSChars(HashSet<SymCharToken> contained) {
        InitContainedSChars();
        foreach (var v in containedSChars) {
            contained.Add(v);
        }
    }

    public override void CollectSymbols(NonTermSet nonTermSet, HashSet<CharToken> alphabet) {
        Left.CollectSymbols(nonTermSet, alphabet);
        Right.CollectSymbols(nonTermSet, alphabet);
    }

    public override HashSet<NamedStrToken> ContainedVars() {
        InitContainedVars();
        return containedVars;
    }

    public override MinTerms FirstMinTerms() {
        InitFirstCandidates();
        return firstChars;
    }

    public override MinTerms LastMinTerms() {
        InitLastCandidates();
        return lastChars;
    }

    public static bool IsBalanced(Str left, Str right) =>
        Math.Abs((int)left.Level - (int)right.Level) <= 1;

    public TupleStr(Str left, Str right) : this(uint.MaxValue, left, right) {
        // temporal chunk
        DegenerationLevel = left.DegenerationLevel + right.DegenerationLevel + (IsBalanced(left, right) ? 0 : 1);
    }

    public TupleStr(uint chunkId, Str left, Str right) : base(chunkId) {
        Left = left;
        Right = right;
        Length = left.Length + right.Length;
        Level = Math.Max(left.Level, right.Level) + 1;
        Ground = left.Ground && right.Ground;
        RegexFree = left.RegexFree && right.RegexFree;
        Derivable = left.Derivable && (!left.Nullable || right.Derivable);
        Nullable = left.Nullable && right.Nullable;
        BasicRegex = left.BasicRegex && right.BasicRegex;
        DegenerationLevel = ComputeDegeneration(left, right);
    }

    static int ComputeDegeneration(Str left, Str right) =>
        left.DegenerationLevel + right.DegenerationLevel + (IsBalanced(left, right) ? 0 : 1);

    public override TupleStr Translate(StrManager manager) {
        var left = Left.Translate(manager);
        var right = Right.Translate(manager);
        return (TupleStr)manager.Concat(left, right);
    }

    public override bool Equals(object? obj) =>
        obj is TupleStr other && Equals(other);

    public override bool Equals(Str? other) =>
        other is TupleStr tc && Equals(tc);

    public bool Equals(TupleStr? other) {
        if (other is null)
            return false;
        if (CachedEquals(other))
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
                    if (CachedEquals(left, right))
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

    public override void MoveCache(Str old) {
        Debug.Assert(!ReferenceEquals(old, this));
        Debug.Assert(old is TupleStr);
        TupleStr oldStr = (TupleStr)old;
        if (containedVars is not null)
            containedVars = oldStr.containedVars;
        if (containedSChars is not null)
            containedSChars = oldStr.containedSChars;
        if (ListCache is not null) {
            ListCache = oldStr.ListCache;
            ListCacheFrom = oldStr.ListCacheFrom;
            ListCacheTo = oldStr.ListCacheTo;
        }
        if (firstChars is not null)
            firstChars = oldStr.firstChars;
        if (lastChars is not null)
            lastChars = oldStr.lastChars;
        if (SimplifyCache is not null)
            SimplifyCache = oldStr.SimplifyCache;
        if (DropLeftCache is not null)
            DropLeftCache = oldStr.DropLeftCache;
        if (DropRightCache is not null)
            DropRightCache = oldStr.DropRightCache;
        if (SubstCache is not null)
            SubstCache = oldStr.SubstCache;
    }

    public override Str Derivative(Environment env, CharacterSet a, bool fwd) {
        Str? result;
        if (fwd) {
            derivativeSetCacheFwd ??= [];
            if (derivativeSetCacheFwd.TryGetValue(a, out result))
                return result;
            var res1 = Left.Derivative(env, a, fwd);
            if (!Left.Nullable) {
                result = env.StrManager.Concat(res1, Right);
            }
            else {
                var res2 = Right.Derivative(env, a, fwd);
                result = env.StrManager.MkUnion([env.StrManager.Concat(res1, Right), res2]);
            }
            derivativeSetCacheFwd.Add(a, result);
        }
        else {
            derivativeSetCacheBwd ??= [];
            if (derivativeSetCacheBwd.TryGetValue(a, out result))
                return result;
            var res1 = Right.Derivative(env, a, fwd);
            if (!Right.Nullable) {
                result = env.StrManager.Concat(Left, res1);
            }
            else {
                var res2 = Left.Derivative(env, a, fwd);
                result = env.StrManager.MkUnion([env.StrManager.Concat(Left, res1), res2]);
            }
            derivativeSetCacheBwd.Add(a, result);
        }
        return result;
    }

    public override string RawString => $"({Left.RawString}{Right.RawString})";

    public override string GetPlainString(NielsenGraph? graph) => Left.GetPlainString(graph) + Right.GetPlainString(graph); 
}