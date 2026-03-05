using Microsoft.Z3;
// Auxiliary contains constraint used internally for rudimentary propagation; simplified
// aggressively because more precise handling happens through regex membership constraints.
using ZIPT.Constraints.Modifier;
using ZIPT.IntUtils;
using ZIPT.MiscUtils;
using ZIPT.Strings.Chunks;
using ZIPT.Strings.Tokens;

namespace ZIPT.Constraints.ConstraintElement.AuxConstraints;

public class StrContains : StrConstraint {

    public bool Negated { get; }
    public Str S { get; }
    public Str Contained { get; }

    public StrContains(Str s, Str contained, bool negated) : base(new DependencyTracker(0)) {
        Negated = negated;
        S = s;
        Contained = contained;
    }

    public override bool Equals(object? obj) =>
        obj is StrContains contains && Equals(contains);

    public bool Equals(StrContains other) =>
        Negated == other.Negated && S.Equals(other.S) && Contained.Equals(other.Contained);

    public override int GetHashCode() =>
        585100949 * HashCode.Combine(Negated, S, Contained);

    public override string ToString() => $"{(Negated ? "!" : "")}Contains({S}, {Contained})";

    public override StrContains Apply(Subst subst, NielsenNode node) =>
        new(node.Env.StrManager.Subst(S, subst),
            node.Env.StrManager.Subst(Contained, subst), Negated);
    
    public override StrContains Apply(CharSubst subst, NielsenNode node) =>
        new(node.Env.StrManager.Subst(node.Env, S, subst),
            node.Env.StrManager.Subst(node.Env, Contained, subst), Negated);

    public override StrContains Apply(Interpretation itp) =>
        new(itp.Env.StrManager.Subst(S, itp),
            itp.Env.StrManager.Subst(Contained, itp), Negated);

    // Just very rudimentary implementation - it will get eliminated anyway...
    protected override SimplifyResult SimplifyAndPropagateInternal(LocalInfo info, DetModifier sConstr,
        ref BacktrackReasons reason) {
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

    public override BoolExpr ToExpr(Environment env, Dictionary<NamedStrToken, int> currentModificationCnt) => 
        (BoolExpr)env.ContainsFct.Apply(S.ToExpr(env, currentModificationCnt), Contained.ToExpr(env, currentModificationCnt));

    public override void CollectSymbols(NonTermSet nonTermSet, CharacterSet alphabet) {
        S.CollectSymbols(nonTermSet, alphabet);
        Contained.CollectSymbols(nonTermSet, alphabet);
    }

    public override bool Contains(NamedStrToken namedStrToken) => 
        S.ContainsVar(namedStrToken) || Contained.ContainsVar(namedStrToken);

    public override ModifierBase Extend(LocalInfo info, Dictionary<NamedInt, PDD<BigRational>> intSubst) => 
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