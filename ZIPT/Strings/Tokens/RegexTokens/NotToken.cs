using Microsoft.Z3;
using System.Text;
using ZIPT.Constraints;
using ZIPT.MiscUtils;
using ZIPT.Strings.Chunks;

namespace ZIPT.Strings.Tokens.RegexTokens;

public sealed class NotToken : StrToken {

    public Str Base { get; }
    
    public override bool Ground => Base.Ground;
    public override bool RegexFree => false;
    public override bool Derivable => true;
    public override bool Nullable => !Base.Nullable;
    public override bool BasicRegex => false;

    public NotToken(Str @base) => 
        Base = @base;

    public override List<StrDecomposition> GetDecomposition(NielsenNode node, bool fwd) => 
        throw new NotSupportedException();

    public override Expr ToExpr(Environment env, Dictionary<NamedStrToken, int> currentModificationCnt) =>
        env.CompFct.Apply(Base.ToExpr(env, currentModificationCnt));

    protected override int CompareToInternal(StrToken other) => 
        Base.CompareTo(((NotToken)other).Base);

    public override void CollectSymbols(NonTermSet nonTermSet, CharacterSet alphabet) => 
        Base.CollectSymbols(nonTermSet, alphabet);

    // THIS IS NOT THE COMPLEMENT OF THE MINTERMS
    public override MinTerms FirstMinTerms() => Base.FirstMinTerms().Complete();

    public override MinTerms LastMinTerms() => Base.LastMinTerms().Complete();

    public override bool Equals(StrToken? other) => 
        other is NotToken k && Base.Equals(k.Base);

    public override int GetHashCode() =>
        723062831 * Base.GetHashCode();

    public override string ToString(NielsenGraph? graph) {
        StringBuilder sb = new();
        string s = Base.ToString(graph);
        if (s.Length == 1)
            sb.Append("~").Append(s);
        else
            sb.Append("~(").Append(Base).Append(")");
        return sb.ToString();
    }

    public override Str Derivative(Environment env, CharacterSet set, bool fwd) =>
        env.StrManager.MkComplement(Base.Derivative(env, set, fwd));

    // we should not require this
}