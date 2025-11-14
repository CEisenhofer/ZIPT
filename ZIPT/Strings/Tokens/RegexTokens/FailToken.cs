using Microsoft.Z3;
using ZIPT.Constraints;
using ZIPT.MiscUtils;
using ZIPT.Strings.Chunks;

namespace ZIPT.Strings.Tokens.RegexTokens;

// TODO: Replace this by an empty character set token
public sealed class FailToken : StrToken {
    public override bool Ground => true;
    public override bool RegexFree => false;
    public override bool Derivable => true;
    public override bool Nullable => false;
    public override bool BasicRegex => false;

    public FailToken() { }

    public override List<StrDecomposition> GetDecomposition(NielsenNode node, bool fwd) => 
        throw new NotSupportedException();

    public override Expr ToExpr(Environment env, Dictionary<NamedStrToken, int> currentModificationCnt) => env.Fail;

    protected override int CompareToInternal(StrToken other) => 0;

    public override void CollectSymbols(NonTermSet nonTermSet, HashSet<CharToken> alphabet) { }

    public override MinTerms FirstMinTerms() => new();

    public override MinTerms LastMinTerms() => new();

    public override bool Equals(StrToken? other) => other is FailToken;

    public override int GetHashCode() => 389639123;

    public override string ToString(NielsenGraph? graph) => "!";

    public override Str Derivative(Environment env, CharacterSet set, bool fwd) => env.FailStr;
}