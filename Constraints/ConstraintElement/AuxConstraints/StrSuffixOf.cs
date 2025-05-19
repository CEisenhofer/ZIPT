using Microsoft.Z3;
using ZIPT.Constraints.Modifier;
using ZIPT.IntUtils;
using ZIPT.Tokens;

namespace ZIPT.Constraints.ConstraintElement.AuxConstraints;

public class StrSuffixOf : StrConstraint {

    public bool Negated { get; }
    public Str S { get; }
    public Str Contained { get; }

    public StrSuffixOf(Str s, Str contained, bool negated) {
        Negated = negated;
        S = s;
        Contained = contained;
    }

    public override StrSuffixOf Clone() => new(S.Clone(), Contained.Clone(), Negated);

    public override bool Equals(object? obj) =>
        obj is StrSuffixOf suffixOf && Equals(suffixOf);

    public bool Equals(StrSuffixOf other) =>
        Negated == other.Negated && S.Equals(other.S) && Contained.Equals(other.Contained);

    public override int GetHashCode() =>
        729998201 * HashCode.Combine(Negated, S, Contained);

    public override string ToString() => $"{(Negated ? "!" : "")}SuffixOf({Contained}, {S})";

    public override void Apply(Subst subst) {
        S.Apply(subst);
        Contained.Apply(subst);
    }

    public override void Apply(Interpretation itp) {
        S.Apply(itp);
        Contained.Apply(itp);
    }

    // Just very rudimentary implementation - it will get eliminated anyway...
    protected override SimplifyResult SimplifyAndPropagateInternal(NielsenNode node, DetModifier sConstr,
        ref BacktrackReasons reason) {
        if (S.Count < Contained.Count)
            return SimplifyResult.Proceed;
        int i = Contained.Count;
        for (; i > 0 && S[i - 1] is CharToken c1 && Contained[i - 1] is CharToken c2; i--) {
            if (c1.Equals(c2)) 
                continue;
            if (Negated)
                return SimplifyResult.Satisfied;
            reason = BacktrackReasons.SymbolClash;
            return SimplifyResult.Conflict;
        }
        for (; i > 0; i--) {
            if (!S[i - 1].Equals(Contained[i - 1]))
                return SimplifyResult.Proceed;
        }
        return Negated ? SimplifyResult.Conflict : SimplifyResult.Satisfied;
    }

    public override BoolExpr ToExpr(NielsenGraph graph) => 
        (BoolExpr)graph.Cache.SuffixOfFct.Apply(Contained.ToExpr(graph), S.ToExpr(graph));

    public override void CollectSymbols(NonTermSet nonTermSet, HashSet<CharToken> alphabet) {
        S.CollectSymbols(nonTermSet, alphabet);
        Contained.CollectSymbols(nonTermSet, alphabet);
    }

    public override StrSuffixOf Negate() =>
        new(S.Clone(), Contained.Clone(), !Negated);

    public override bool Contains(NamedStrToken namedStrToken) => 
        S.Contains(namedStrToken) || Contained.Contains(namedStrToken);

    public override ModifierBase Extend(NielsenNode node, Dictionary<NonTermInt, RatPoly> intSubst) => 
        throw new NotSupportedException();

    public override int CompareToInternal(StrConstraint other) {
        StrSuffixOf otherSuffixOf = (StrSuffixOf)other;
        int cmp = Negated.CompareTo(otherSuffixOf.Negated);
        if (cmp != 0)
            return cmp;
        cmp = S.CompareTo(otherSuffixOf.S);
        return cmp != 0 ? cmp : Contained.CompareTo(otherSuffixOf.Contained);
    }
}