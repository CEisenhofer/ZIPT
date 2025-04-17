using Microsoft.Z3;
using StringBreaker.Constraints.Modifier;
using StringBreaker.IntUtils;
using StringBreaker.MiscUtils;
using StringBreaker.Tokens;

namespace StringBreaker.Constraints.ConstraintElement;

public abstract class Constraint {

    public bool Satisfied { get; private set; }
    
    public abstract Constraint Clone();
    public abstract override bool Equals(object? obj);
    public abstract override int GetHashCode();
    public abstract override string ToString();

    public abstract void Apply(Subst subst);
    public abstract void Apply(Interpretation itp);

    public SimplifyResult SimplifyAndPropagate(NielsenNode node, DetModifier sConstr, ref BacktrackReasons reason) {
        var res = SimplifyAndPropagateInternal(node, sConstr, ref reason);
        if (res is SimplifyResult.Satisfied or SimplifyResult.RestartAndSatisfied)
            Satisfied = true;
        return res;
    }

    protected abstract SimplifyResult SimplifyAndPropagateInternal(NielsenNode node, DetModifier sConstr, ref BacktrackReasons reason);
    public abstract BoolExpr ToExpr(NielsenGraph graph);
    public abstract void CollectSymbols(HashSet<NamedStrToken> vars, HashSet<SymCharToken> sChars, HashSet<IntVar> iVars, HashSet<CharToken> alphabet);
    public abstract Constraint Negate();
}