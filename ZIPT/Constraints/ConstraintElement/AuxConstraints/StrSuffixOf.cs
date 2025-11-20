using Microsoft.Z3;
using ZIPT.Constraints.Modifier;
using ZIPT.IntUtils;
using ZIPT.MiscUtils;
using ZIPT.Strings.Chunks;
using ZIPT.Strings.Tokens;

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

    public override bool Equals(object? obj) =>
        obj is StrSuffixOf suffixOf && Equals(suffixOf);

    public bool Equals(StrSuffixOf other) =>
        Negated == other.Negated && S.Equals(other.S) && Contained.Equals(other.Contained);

    public override int GetHashCode() =>
        729998201 * HashCode.Combine(Negated, S, Contained);

    public override string ToString() => $"{(Negated ? "!" : "")}SuffixOf({Contained}, {S})";

    public override StrSuffixOf Apply(Subst subst, NielsenNode node) =>
        new(node.Env.StrManager.Subst(S, subst),
            node.Env.StrManager.Subst(Contained, subst), Negated);
    
    public override StrSuffixOf Apply(CharSubst subst, NielsenNode node) =>
        new(node.Env.StrManager.Subst(node.Env, S, subst),
            node.Env.StrManager.Subst(node.Env, Contained, subst), Negated);

    public override StrSuffixOf Apply(Interpretation itp) =>
        new(itp.Env.StrManager.Subst(S, itp),
            itp.Env.StrManager.Subst(Contained, itp), Negated);

    // Just very rudimentary implementation - it will get eliminated anyway...
    protected override SimplifyResult SimplifyAndPropagateInternal(LocalInfo info, DetModifier sConstr,
        ref BacktrackReasons reason) {
        if (S.Length < Contained.Length)
            return SimplifyResult.Proceed;
        int i = (int)Contained.Length;
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

    public override BoolExpr ToExpr(Environment env, Dictionary<NamedStrToken, int> currentModificationCnt) => 
        (BoolExpr)env.SuffixOfFct.Apply(Contained.ToExpr(env, currentModificationCnt), S.ToExpr(env, currentModificationCnt));

    public override void CollectSymbols(NonTermSet nonTermSet, CharacterSet alphabet) {
        S.CollectSymbols(nonTermSet, alphabet);
        Contained.CollectSymbols(nonTermSet, alphabet);
    }

    public override StrSuffixOf Negate() => new(S, Contained, !Negated);

    public override bool Contains(NamedStrToken namedStrToken) => 
        S.ContainsVar(namedStrToken) || Contained.ContainsVar(namedStrToken);

    public override ModifierBase? Extend(LocalInfo info, Dictionary<NamedInt, PDD<BigRational>> intSubst) => 
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