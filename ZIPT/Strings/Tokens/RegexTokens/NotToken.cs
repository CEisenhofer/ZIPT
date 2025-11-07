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

    public override Expr ToExpr(NielsenGraph graph) =>
        graph.Env.CompFct.Apply(Base.ToExpr(graph));

    protected override int CompareToInternal(StrToken other) => 
        Base.CompareTo(((KleeneToken)other).Base);

    public override void CollectSymbols(NonTermSet nonTermSet, HashSet<CharToken> alphabet) => 
        Base.CollectSymbols(nonTermSet, alphabet);

    public override MinTerms FirstMinTerms() => Base.FirstMinTerms().Complement();

    public override MinTerms LastMinTerms() => Base.LastMinTerms().Complement();

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
}