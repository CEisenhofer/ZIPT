using Microsoft.Z3;
using System.Diagnostics;
using ZIPT.Constraints;
using ZIPT.MiscUtils;
using ZIPT.Strings.Chunks;

namespace ZIPT.Strings.Tokens.RegexTokens;

public sealed class SetToken : UnitToken {

    public CharacterSet Set { get; }

    public override bool RegexFree => false;
    public override bool Derivable => true;
    public override bool Ground => true;
    public override bool Nullable => false;
    public override bool BasicRegex => !Set.IsEmpty;

    public SetToken(CharacterSet set) {
        Set = set;
    }

    static Expr RangeToExpr(NielsenGraph graph, CharacterRange range) {
        if (range.IsUnit)
            return new CharToken(range.From).ToExpr(graph);
        Debug.Assert(range.From < range.To);
        return graph.Env.RgFct.Apply(
            new CharToken(range.From).ToExpr(graph),
            new CharToken(range.To).ToExpr(graph));
    }

    public override Expr ToExpr(NielsenGraph graph) {
        Debug.Assert(!Set.IsEmpty);
        Expr expr = RangeToExpr(graph, Set.Ranges[^1]);
        for (int i = Set.Ranges.Count - 1; i > 0; i--) {
            var e = RangeToExpr(graph, Set.Ranges[i - 1]);
            expr = graph.Env.UnionFct.Apply(e, expr);
        }
        return expr;
    }

    protected override int CompareToInternal(StrToken other) => 
        other is SetToken s ? Set.CompareTo(s.Set) : 0;

    public override void CollectSymbols(NonTermSet nonTermSet, HashSet<CharToken> alphabet) {
        throw new NotImplementedException();
    }

    public override MinTerms FirstMinTerms() => new(Set);

    public override MinTerms LastMinTerms() => new(Set);

    public override bool Equals(StrToken? other) => other is SetToken s && Set.Equals(s.Set);

    public override int GetHashCode() => Set.GetHashCode();

    public override string ToString(NielsenGraph? graph) => Set.ToString();

    public override Str Derivative(Environment env, CharacterSet set, bool fwd) =>
        !set.IsDisjoint(Set) ? env.EmptyStr : env.FailStr;
}