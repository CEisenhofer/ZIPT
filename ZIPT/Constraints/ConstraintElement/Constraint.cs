using Microsoft.Z3;
using System.Diagnostics.Contracts;
using ZIPT.Constraints.Modifier;
using ZIPT.MiscUtils;
using ZIPT.Strings.Tokens;

namespace ZIPT.Constraints.ConstraintElement;

public abstract class Constraint {

    // Base class for all constraints handled by the Nielsen search (string equalities,
    // membership, integer equalities/inequalities). Provides a common simplify/propagate
    // entry point and conversion to Z3 expressions.

    public bool Satisfied { get; private set; }
    public DependencyTracker Reason { get; protected set; }
    public abstract bool Shared { get; }

    protected Constraint(DependencyTracker reason) {
        Reason = reason;
    }

    public abstract override bool Equals(object? obj);
    public abstract override int GetHashCode();
    public abstract override string ToString();

    [Pure]
    public abstract Constraint Apply(Subst subst, NielsenNode node);
    [Pure]
    public abstract Constraint Apply(CharSubst subst, NielsenNode node);

    [Pure]
    public abstract Constraint Apply(Interpretation itp);

    public SimplifyResult SimplifyAndPropagate(LocalInfo info, NonTermSet modSet, DetModifier outSideCnstr, ref BacktrackReasons reason) {
        // if (!force && !NonTermSet.IsIntersecting(modSet, Dependencies)) {
        //     // No reason to evaluate; we assume we already did all rewriting applicable without having more knowledge
        //     // If the last step did not change any variable involved, no reason to reevaluate this constraint
        //     // force => initially we can have constraints that need simplification without having any knowledge
        //     return SimplifyResult.Proceed;
        // }
        var res = SimplifyAndPropagateInternal(info, outSideCnstr, ref reason);
        if (res is SimplifyResult.Satisfied or SimplifyResult.RestartAndSatisfied)
            Satisfied = true;
        return res;
    }

    protected abstract SimplifyResult SimplifyAndPropagateInternal(LocalInfo info, DetModifier sConstr, ref BacktrackReasons reason);
    public abstract BoolExpr ToExpr(Environment env, Dictionary<NamedStrToken, int> currentModificationCnt);
    public BoolExpr ToExpr(LocalInfo info) => ToExpr(info.Env, info.CurrentModificationCnt);
    public abstract void CollectSymbols(NonTermSet nonTermSet, CharacterSet alphabet);
}