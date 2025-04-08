using Microsoft.Z3;
using StringBreaker.Constraints.Modifier;
using StringBreaker.IntUtils;
using StringBreaker.Strings;
using StringBreaker.Strings.Tokens;

namespace StringBreaker.Constraints.ConstraintElement.AuxConstraints;

public class StrContains : StrConstraint {

    public bool Negated { get; }
    public Str S { get; }
    public Str Contained { get; }

    public StrContains(Str s, Str contained, bool negated) {
        Negated = negated;
        S = s;
        Contained = contained;
    }

    public override StrContains Clone(NielsenContext ctx) => new(S.ShallowClone(), Contained.ShallowClone(), Negated);

    public override bool Equals(object? obj) =>
        obj is StrContains contains && Equals(contains);

    public bool Equals(StrContains other) =>
        Negated == other.Negated && S.Equals(other.S) && Contained.Equals(other.Contained);

    public override int GetHashCode() =>
        585100949 * HashCode.Combine(Negated, S, Contained);

    public override string ToString() => $"{(Negated ? "!" : "")}Contains({S}, {Contained})";

    public override void Apply(Subst subst) {
        S.Apply(subst);
        Contained.Apply(subst);
    }

    public override void Apply(Interpretation itp) {
        S.Apply(itp);
        Contained.Apply(itp);
    }

    // Just very rudimentary implementation - it will get eliminated anyway...
    protected override SimplifyResult SimplifyInternal(NielsenContext ctx, List<Subst> newSubst, HashSet<Constraint> newSideConstr, ref BacktrackReasons reason) {
        if (S.Count < Contained.Count)
            return SimplifyResult.Proceed;
        int i = 0;
        for (; i < Contained.Count && S[i] is CharToken c1 && Contained[i] is CharToken c2; i++) {
            if (c1.Equals(c2)) 
                continue;
            if (Negated)
                return SimplifyResult.Satisfied;
            reason = BacktrackReasons.SymbolClash;
            return SimplifyResult.Conflict;
        }
        for (; i < Contained.Count; i++) {
            if (!S[i].Equals(Contained[i]))
                return SimplifyResult.Proceed;
        }
        return Negated ? SimplifyResult.Conflict : SimplifyResult.Satisfied;
    }

    public override BoolExpr ToExpr(NielsenContext ctx) => 
        (BoolExpr)ctx.Cache.ContainsFct.Apply(S.ToExpr(ctx), Contained.ToExpr(ctx));

    public override void CollectSymbols(HashSet<NamedStrToken> vars, HashSet<SymCharToken> sChars, HashSet<IntVar> iVars, HashSet<CharToken> alphabet) {
        S.CollectSymbols(vars, sChars, iVars, alphabet);
        Contained.CollectSymbols(vars, sChars, iVars, alphabet);
    }

    public override StrContains Negate(NielsenContext ctx) =>
        new(S.ShallowClone(), Contained.ShallowClone(), !Negated);

    public override bool Contains(NamedStrToken namedStrToken) => 
        S.Contains(namedStrToken) || Contained.Contains(namedStrToken);

    public override ModifierBase Extend(NielsenContext ctx) => 
        throw new NotSupportedException();

    public override int CompareToInternal(StrConstraint other) {
        StrContains otherContains = (StrContains)other;
        int cmp = Negated.CompareTo(otherContains.Negated);
        if (cmp != 0)
            return cmp;
        cmp = S.CompareTo(otherContains.S);
        return cmp != 0 ? cmp : Contained.CompareTo(otherContains.Contained);
    }
}