using ZIPT.Constraints;
using ZIPT.MiscUtils;
using ZIPT.Strings.Tokens;

namespace ZIPT.Strings.Chunks;

public sealed class SingletonStr : Str, IEquatable<SingletonStr> {
    public StrToken StrToken { get; }
    public SingletonStr(uint chunkId, StrToken token) : base(chunkId) {
        StrToken = token;
        Ground = StrToken.Ground;
        RegexFree = StrToken.RegexFree;
        Derivable = StrToken.Derivable;
        Nullable = StrToken.Nullable;
        BasicRegex = StrToken.BasicRegex;
        DegenerationLevel = 0;
    }

    public override uint Length => 1;
    public override uint Level => 1;
    public override bool ContainsVar(NamedStrToken v) =>
        StrToken is NamedStrToken vt && vt.Equals(v);

    public override void CollectVars(HashSet<NamedStrToken> contained) {
        if (StrToken is NamedStrToken vt)
            contained.Add(vt);
    }

    public override bool ContainsSChar(SymCharToken v) =>
        StrToken is UnitToken vt && vt.Equals(v);

    public override void CollectSChars(HashSet<SymCharToken> contained) {
        if (StrToken is SymCharToken vc)
            contained.Add(vc);
    }

    public override void CollectSymbols(NonTermSet nonTermSet, HashSet<CharToken> alphabet) =>
        StrToken.CollectSymbols(nonTermSet, alphabet);

    public override HashSet<NamedStrToken> ContainedVars() {
        HashSet<NamedStrToken> tokens = [];
        CollectVars(tokens);
        return tokens;
    }

    public override MinTerms FirstMinTerms() => 
        StrToken.FirstMinTerms();

    public override MinTerms LastMinTerms() =>
        StrToken.LastMinTerms();

    public override SingletonStr Translate(StrManager manager) =>
        manager.Single(StrToken);

    public override bool Equals(object? obj) => 
        ReferenceEquals(this, obj) || obj is SingletonStr other && Equals(other);

    public override bool Equals(Str? other) =>
        other is SingletonStr s && StrToken.Equals(s.StrToken);

    public bool Equals(SingletonStr? other) =>
        other is not null && StrToken.Equals(other.StrToken);

    public override int GetHashCode() => StrToken.GetHashCode();

    public override void MoveCache(Str old) { }

    public override Str Derivative(Environment env, CharacterSet a, bool fwd) {
        Str? result;
        if (fwd) {
            derivativeSetCacheFwd ??= [];
            if (!derivativeSetCacheFwd.TryGetValue(a, out result)) {
                result = StrToken.Derivative(env, a, fwd);
                derivativeSetCacheFwd[a] = result;
            }
        }
        else {
            derivativeSetCacheBwd ??= [];
            if (!derivativeSetCacheBwd.TryGetValue(a, out result)) {
                result = StrToken.Derivative(env, a, fwd);
                derivativeSetCacheBwd[a] = result;
            }
        }
        return result;
    }

    public override string RawString => StrToken.ToString();
    public override string GetPlainString(NielsenGraph? graph) => StrToken.ToString(graph);
}