using Microsoft.Z3;
using StringBreaker.IntUtils;
using StringBreaker.Tokens;

namespace StringBreaker.Constraints.ConstraintElement;

public abstract class Constraint {

    public bool Satisfied { get; private set; }
    public bool Violated { get; private set; }
    
    public abstract Constraint Clone();
    public abstract override bool Equals(object? obj);
    public abstract override int GetHashCode();
    public abstract override string ToString();

    public abstract void Apply(Subst subst);
    public abstract void Apply(Interpretation itp);

    public SimplifyResult Simplify(NielsenNode node, List<Subst> substitution, HashSet<Constraint> newSideConstraints, ref BacktrackReasons reason) {
        var res = SimplifyInternal(node, substitution, newSideConstraints, ref reason);
        if (res == SimplifyResult.Conflict)
            Violated = true;
        else if (res is SimplifyResult.Satisfied or SimplifyResult.RestartAndSatisfied)
            Satisfied = true;
        return res;
    }

    protected abstract SimplifyResult SimplifyInternal(NielsenNode node,
        List<Subst> newSubst, HashSet<Constraint> newSideConstr, ref BacktrackReasons reason);
    public abstract BoolExpr ToExpr(NielsenGraph graph);
    public abstract void CollectSymbols(HashSet<NamedStrToken> vars, HashSet<SymCharToken> sChars, HashSet<IntVar> iVars, HashSet<CharToken> alphabet);
    public abstract Constraint Negate();
}