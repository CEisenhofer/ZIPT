using Microsoft.Z3;
using ZIPT.IntUtils;
using ZIPT.MiscUtils;
using ZIPT.Constraints.Modifier;
using ZIPT.Tokens;

namespace ZIPT.Constraints.ConstraintElement;

public abstract class Constraint {

    // There is no problem if this set contains elements that are not actually present (anymore)
    // Used only to detect if there is potential need to rewrite constraint
    // e.g., x / u does not require a constraint to be rewritten if it does not contain x...
    public NonTermSet Dependencies { get; } = new();

    public bool Satisfied { get; private set; }
    
    public abstract Constraint Clone();
    public abstract override bool Equals(object? obj);
    public abstract override int GetHashCode();
    public abstract override string ToString();

    public abstract void Apply(Subst subst);
    public abstract void Apply(Interpretation itp);

    public SimplifyResult SimplifyAndPropagate(NielsenNode node, NonTermSet modSet, DetModifier outSideCnstr, ref BacktrackReasons reason, bool force) {
        //if (!force && !NonTermSet.IsIntersecting(modSet, Dependencies)) {
        //    // No reason to evaluate; we assume we already did all rewriting applicable without having more knowledge
        //    // If the last step did not change any variable involved, no reason to reevaluate this constraint
        //    // force => initially we can have constraints that need simplification without having any knowledge
        //    return SimplifyResult.Proceed;
        //}
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