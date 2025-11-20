using System.Diagnostics;
using Microsoft.Z3;
using System.Text;
using ZIPT.Constraints;
using ZIPT.MiscUtils;
using ZIPT.Strings.Chunks;

namespace ZIPT.Strings.Tokens.RegexTokens;

public sealed class KleeneToken : StrToken {
    public Str Base { get; }

    public override bool Ground => Base.Ground;
    public override bool RegexFree => false;
    public override bool Derivable => true;
    public override bool Nullable => true;
    public override bool BasicRegex { get; }

    public KleeneToken(Str @base) {
        Debug.Assert(@base is not { Length: 1, First: KleeneToken });
        Base = @base;
        BasicRegex = @base.BasicRegex;
    }

    public override List<StrDecomposition> GetDecomposition(NielsenNode node, bool fwd) {
        throw new NotSupportedException();
#if false
        Str starStr = node.Env.MkString(this);

        var decompositions = StrManager.GetDecompose(node, Base, fwd);

        // for the first case, we ignore the postfix (otw. we would have at least one iteration of star)
        decompositions[0].Prefix = node.Env.StrManager.Concat(starStr, decompositions[0].Prefix, fwd);
        decompositions[0].Postfix = starStr;

        for (int i = 1; i < decompositions.Count; i++) {
            decompositions[i].Prefix = node.Env.StrManager.Concat(starStr, decompositions[i].Prefix, fwd);
            decompositions[i].Postfix = node.Env.StrManager.Concat(decompositions[i].Postfix, starStr, fwd);
        }

        return decompositions;
#endif
    }

    public override Expr ToExpr(Environment env, Dictionary<NamedStrToken, int> currentModificationCnt) {
        var e = Base.ToExpr(env, currentModificationCnt);
        /*if (e is ReExpr r)
            return graph.Ctx.MkStar(r);
        return graph.Ctx.MkStar(graph.Ctx.MkToRe((SeqExpr)e));*/
        return env.StarFct.Apply(e);
    }

    protected override int CompareToInternal(StrToken other) => 
        Base.CompareTo(((KleeneToken)other).Base);

    public override void CollectSymbols(NonTermSet nonTermSet, CharacterSet alphabet) => 
        Base.CollectSymbols(nonTermSet, alphabet);

    public override MinTerms FirstMinTerms() => Base.FirstMinTerms();

    public override MinTerms LastMinTerms() => Base.LastMinTerms();

    public override bool Equals(StrToken? other) => 
        other is KleeneToken k && Base.Equals(k.Base);

    public override int GetHashCode() =>
        741354643 * Base.GetHashCode();

    public override string ToString(NielsenGraph? graph) {
        StringBuilder sb = new();
        string s = Base.ToString();
        if (s.Length > 1)
            sb.Append('(').Append(s).Append(")*");
        else
            sb.Append(s).Append('*');
        return sb.ToString();
    }

    public override Str Derivative(Environment env, CharacterSet set, bool fwd) {
        var der = Base.Derivative(env, set, fwd);
        return env.StrManager.Concat(der, env.MkString(this));
    }

}