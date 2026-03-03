using Microsoft.Z3;
using System.Diagnostics;
using ZIPT.Constraints;
using ZIPT.MiscUtils;
using ZIPT.Strings.Chunks;

namespace ZIPT.Strings.Tokens.RegexTokens;

// Token representing a set/range of characters. Used for character-range reasoning and SMT encoding.
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

    static Expr RangeToExpr(Environment env, CharacterRange range) {
        if (range.IsUnit)
            return new CharToken(range.From).ToExpr(env);
        Debug.Assert(range.From < range.To);
        return env.RgFct.Apply(
            new CharToken(range.From).ToExpr(env),
            new CharToken(range.To - 1).ToExpr(env));
    }

    public override Expr ToExpr(Environment env, Dictionary<NamedStrToken, int> currentModificationCnt) {
        Debug.Assert(!Set.IsEmpty);
        Expr expr = RangeToExpr(env, Set.Ranges[^1]);
        for (int i = Set.Ranges.Count - 1; i > 0; i--) {
            var e = RangeToExpr(env, Set.Ranges[i - 1]);
            expr = env.UnionFct.Apply(e, expr);
        }
        return expr;
    }

    public BoolExpr ToIntBounds(Environment env, Expr e) {
        if (Set.IsEmpty)
            return env.Ctx.MkFalse();
        BitVecExpr bv = (BitVecExpr)env.ValOf.Apply(e);
        List<BoolExpr> ranges = [];
        foreach (var r in Set.Ranges) {
            Debug.Assert(r.From < r.To);
            ranges.Add(env.Ctx.MkAnd(
                env.Ctx.MkBVULE(env.Ctx.MkBV(r.From, Options.CharBits), bv),
                env.Ctx.MkBVULE(bv, env.Ctx.MkBV(r.To - 1, Options.CharBits))));
        }
        return env.Ctx.MkOr(ranges);
    }

    protected override int CompareToInternal(StrToken other) => 
        other is SetToken s ? Set.CompareTo(s.Set) : 0;

    public override void CollectSymbols(NonTermSet nonTermSet, CharacterSet alphabet) => alphabet.Add(Set);

    public override MinTerms FirstMinTerms() => new(Set);

    public override MinTerms LastMinTerms() => new(Set);

    public override bool Equals(StrToken? other) => other is SetToken s && Set.Equals(s.Set);

    public override int GetHashCode() => Set.GetHashCode();

    public override string ToString(NielsenGraph? graph) => Set.ToString();

    public override Str Derivative(Environment env, CharacterSet set, bool fwd) =>
        !set.IsDisjoint(Set) ? env.EmptyStr : env.FailStr;
    // SetToken represents an explicit character set used in regexes; derivative succeeds
    // only when the consumed set is fully included.

}