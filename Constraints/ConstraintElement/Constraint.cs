using Microsoft.Z3;
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
    public abstract void Apply(Interpretation subst);

    public SimplifyResult Simplify(NielsenNode node, List<Subst> substitution, HashSet<Constraint> newSideConstraints) {
        var res = SimplifyInternal(node, substitution, newSideConstraints);
        if (res == SimplifyResult.Conflict)
            Violated = true;
        else if (res == SimplifyResult.Satisfied)
            Satisfied = true;
        return res;
    }

    protected abstract SimplifyResult SimplifyInternal(NielsenNode node, 
        List<Subst> newSubst, HashSet<Constraint> newSideConstr);
    public abstract BoolExpr ToExpr(NielsenGraph graph);
    public abstract void CollectSymbols(HashSet<StrVarToken> vars, HashSet<CharToken> alphabet);
}