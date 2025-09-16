using System.Diagnostics;
using System.Diagnostics.Contracts;
using Microsoft.Z3;
using ZIPT.Constraints.Modifier;
using ZIPT.Strings.Tokens;

namespace ZIPT.Constraints.ConstraintElement;

public abstract class Constraint {

    public bool Satisfied { get; private set; }

    public abstract override bool Equals(object? obj);
    public abstract override int GetHashCode();
    public abstract override string ToString();

    [Pure]
    public abstract Constraint Apply(Subst subst, NielsenNode node);
    [Pure]
    public abstract Constraint Apply(Interpretation itp);

    public SimplifyResult SimplifyAndPropagate(NielsenNode node, NonTermSet modSet, DetModifier outSideCnstr, ref BacktrackReasons reason, bool force) {
        // if (!force && !NonTermSet.IsIntersecting(modSet, Dependencies)) {
        //     // No reason to evaluate; we assume we already did all rewriting applicable without having more knowledge
        //     // If the last step did not change any variable involved, no reason to reevaluate this constraint
        //     // force => initially we can have constraints that need simplification without having any knowledge
        //     return SimplifyResult.Proceed;
        // }
        var res = SimplifyAndPropagateInternal(node, outSideCnstr, ref reason);
        if (res is SimplifyResult.Satisfied or SimplifyResult.RestartAndSatisfied)
            Satisfied = true;
        return res;
    }

    protected abstract SimplifyResult SimplifyAndPropagateInternal(NielsenNode node, DetModifier sConstr, ref BacktrackReasons reason);
    public abstract BoolExpr ToExpr(NielsenGraph graph);
    public abstract void CollectSymbols(NonTermSet nonTermSet, HashSet<CharToken> alphabet);
    public abstract Constraint Negate();
}