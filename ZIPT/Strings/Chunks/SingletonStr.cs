using ZIPT.Constraints;
using ZIPT.Strings.Tokens;

namespace ZIPT.Strings.Chunks;

public sealed class SingletonStr : Str, IEquatable<SingletonStr> {
    public StrToken StrToken { get; }
    public SingletonStr(uint chunkId, StrToken token) : base(chunkId) {
        StrToken = token;
        Ground = StrToken is not (NamedStrToken or PowerToken { Base.Ground: false });
    }

    public override uint Length => 1;
    public override uint Level => 1;
    public override bool ContainsVar(NamedStrToken v) =>
        StrToken is NamedStrToken vt && vt.Equals(v);

    public override void CollectVars(HashSet<NamedStrToken> contained) {
        if (StrToken is NamedStrToken vt)
            contained.Add(vt);
    }

    public override void CollectSymbols(NonTermSet nonTermSet, HashSet<CharToken> alphabet) {
        switch (StrToken) {
            case NamedStrToken v:
                nonTermSet.Add(v);
                break;
            case CharToken c:
                alphabet.Add(c);
                break;
            case PowerToken p:
                p.Base.CollectSymbols(nonTermSet, alphabet);
                p.Power.CollectSymbols(nonTermSet, alphabet);
                break;
            default:
                throw new NotSupportedException();
        }
    }

    public override SingletonStr Translate(StrManager manager) =>
        manager.Single(StrToken);

    public override StrToken[] Sequence() => 
        [StrToken];

    protected override int CompareToInternal(Str other) =>
        StrToken.CompareTo(((SingletonStr)other).StrToken);

    public override bool Equals(object? obj) {
        return ReferenceEquals(this, obj) || obj is SingletonStr other && Equals(other);
    }

    public override bool Equals(Str? other) =>
        other is SingletonStr s && StrToken.Equals(s.StrToken);

    public bool Equals(SingletonStr? other) =>
        other is not null && StrToken.Equals(other.StrToken);

    public override int GetHashCode() => StrToken.GetHashCode();

    public override string RawString => StrToken.ToString();
    public override string GetPlainString(NielsenGraph? graph) => StrToken.ToString(graph);
}