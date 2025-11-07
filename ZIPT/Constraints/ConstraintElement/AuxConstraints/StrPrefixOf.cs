using Microsoft.Z3;
using ZIPT.Constraints.Modifier;
using ZIPT.IntUtils;
using ZIPT.Strings.Chunks;
using ZIPT.Strings.Tokens;

namespace ZIPT.Constraints.ConstraintElement.AuxConstraints;

public class StrPrefixOf : StrConstraint {

    public bool Negated { get; }
    public Str S { get; set; }
    public Str Contained { get; set; }

    public StrPrefixOf(Str s, Str contained, bool negated) {
        Negated = negated;
        S = s;
        Contained = contained;
    }

    public override bool Equals(object? obj) =>
        obj is StrPrefixOf prefixOf && Equals(prefixOf);

    public bool Equals(StrPrefixOf other) =>
        Negated == other.Negated && S.Equals(other.S) && Contained.Equals(other.Contained);

    public override int GetHashCode() =>
        585100949 * HashCode.Combine(Negated, S, Contained);

    public override string ToString() => $"{(Negated ? "!" : "")}PrefixOf({Contained}, {S})";

    public override StrPrefixOf Apply(Subst subst, NielsenNode node) =>
        new(node.Env.StrManager.Subst(S, subst),
            node.Env.StrManager.Subst(Contained, subst), Negated);

    public override StrPrefixOf Apply(CharSubst subst, NielsenNode node) =>
        new(node.Env.StrManager.Subst(node.Env, S, subst),
            node.Env.StrManager.Subst(node.Env, Contained, subst), Negated);

    public override StrPrefixOf Apply(Interpretation itp) =>
        new(itp.Env.StrManager.Subst(S, itp),
            itp.Env.StrManager.Subst(Contained, itp), Negated);

    // Just very rudimentary implementation - it will get eliminated anyway...
    protected override SimplifyResult SimplifyAndPropagateInternal(NielsenNode node, DetModifier sConstr, ref BacktrackReasons reason) {
        if (S.Length < Contained.Length)
            return SimplifyResult.Proceed;
        int i = 0;
        for (; i < Contained.Length && S[i] is CharToken c1 && Contained[i] is CharToken c2; i++) {
            if (c1.Equals(c2)) 
                continue;
            if (Negated)
                return SimplifyResult.Satisfied;
            reason = BacktrackReasons.SymbolClash;
            return SimplifyResult.Conflict;
        }
        for (; i < Contained.Length; i++) {
            if (!S[i].Equals(Contained[i]))
                return SimplifyResult.Proceed;
        }
        return Negated ? SimplifyResult.Conflict : SimplifyResult.Satisfied;
    }

    public override BoolExpr ToExpr(NielsenGraph graph) => 
        (BoolExpr)graph.Env.PrefixOfFct.Apply(Contained.ToExpr(graph), S.ToExpr(graph));

    public override void CollectSymbols(NonTermSet nonTermSet, HashSet<CharToken> alphabet) {
        S.CollectSymbols(nonTermSet, alphabet);
        Contained.CollectSymbols(nonTermSet, alphabet);
    }

    public override StrPrefixOf Negate() =>
        new(S, Contained, !Negated);

    public override bool Contains(NamedStrToken namedStrToken) => 
        S.ContainsVar(namedStrToken) || Contained.ContainsVar(namedStrToken);

    public override ModifierBase? Extend(NielsenNode node, Dictionary<NamedInt, PDD<BigRational>> intSubst) => 
        throw new NotSupportedException();

    public override int CompareToInternal(StrConstraint other) {
        StrPrefixOf otherPrefixOf = (StrPrefixOf)other;
        int cmp = Negated.CompareTo(otherPrefixOf.Negated);
        if (cmp != 0)
            return cmp;
        cmp = S.CompareTo(otherPrefixOf.S);
        return cmp != 0 ? cmp : Contained.CompareTo(otherPrefixOf.Contained);
    }
}