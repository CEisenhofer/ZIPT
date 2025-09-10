using Microsoft.Z3;
using ZIPT.Constraints.Modifier;
using ZIPT.IntUtils;
using ZIPT.Strings;
using ZIPT.Strings.Tokens;

namespace ZIPT.Constraints.ConstraintElement.AuxConstraints;

public class StrContains : StrConstraint {

    public bool Negated { get; }
    public Str S { get; }
    public Str Contained { get; }

    public StrContains(Str s, Str contained, bool negated) {
        Negated = negated;
        S = s;
        Contained = contained;
    }

    public override StrContains Clone() => new(S, Contained, Negated);

    public override bool Equals(object? obj) =>
        obj is StrContains contains && Equals(contains);

    public bool Equals(StrContains other) =>
        Negated == other.Negated && S.Equals(other.S) && Contained.Equals(other.Contained);

    public override int GetHashCode() =>
        585100949 * HashCode.Combine(Negated, S, Contained);

    public override string ToString() => $"{(Negated ? "!" : "")}Contains({S}, {Contained})";

    public override void Apply(Interpretation itp) {
        S.Apply(itp);
        Contained.Apply(itp);
    }

    // Just very rudimentary implementation - it will get eliminated anyway...
    protected override SimplifyResult SimplifyAndPropagateInternal(NielsenNode node, DetModifier sConstr,
        ref BacktrackReasons reason) {
        if (S.SLength < Contained.SLength)
            return SimplifyResult.Proceed;
        int i = 0;
        for (; i < Contained.SLength && S[i] is CharToken c1 && Contained[i] is CharToken c2; i++) {
            if (c1.Equals(c2)) 
                continue;
            if (Negated)
                return SimplifyResult.Satisfied;
            reason = BacktrackReasons.SymbolClash;
            return SimplifyResult.Conflict;
        }
        for (; i < Contained.SLength; i++) {
            if (!S[i].Equals(Contained[i]))
                return SimplifyResult.Proceed;
        }
        return Negated ? SimplifyResult.Conflict : SimplifyResult.Satisfied;
    }

    public override BoolExpr ToExpr(NielsenGraph graph) => 
        (BoolExpr)graph.Env.ContainsFct.Apply(S.ToExpr(graph), Contained.ToExpr(graph));

    public override void CollectSymbols(NonTermSet nonTermSet, HashSet<CharToken> alphabet) {
        S.CollectSymbols(nonTermSet, alphabet);
        Contained.CollectSymbols(nonTermSet, alphabet);
    }

    public override StrContains Negate() =>
        new(S, Contained, !Negated);

    public override bool Contains(NamedStrToken namedStrToken) => 
        S.Contains(namedStrToken) || Contained.Contains(namedStrToken);

    public override ModifierBase Extend(NielsenNode node, Dictionary<NamedInt, RatPoly> intSubst) => 
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