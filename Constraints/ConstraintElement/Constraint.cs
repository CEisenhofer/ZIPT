using Microsoft.Z3;
using StringBreaker.IntUtils;
using StringBreaker.Strings;
using StringBreaker.Strings.Tokens;

namespace StringBreaker.Constraints.ConstraintElement;

public abstract class Constraint {

    public bool Satisfied { get; private set; }
    public bool Violated { get; private set; }
    
    public abstract Constraint Clone(NielsenContext ctx);
    public abstract override bool Equals(object? obj);
    public abstract override int GetHashCode();
    public abstract override string ToString();

    public abstract void Apply(Subst subst);
    public abstract void Apply(Interpretation itp);

    public SimplifyResult Simplify(NielsenContext ctx, List<Subst> substitution, HashSet<Constraint> newSideConstraints, ref BacktrackReasons reason) {
        var res = SimplifyInternal(ctx, substitution, newSideConstraints, ref reason);
        if (res == SimplifyResult.Conflict)
            Violated = true;
        else if (res is SimplifyResult.Satisfied or SimplifyResult.RestartAndSatisfied)
            Satisfied = true;
        return res;
    }

    protected abstract SimplifyResult SimplifyInternal(NielsenContext ctx,
        List<Subst> newSubst, HashSet<Constraint> newSideConstr, ref BacktrackReasons reason);
    public abstract BoolExpr ToExpr(NielsenContext ctx);
    public abstract void CollectSymbols(HashSet<NamedStrToken> vars, HashSet<SymCharToken> sChars, HashSet<IntVar> iVars, HashSet<CharToken> alphabet);
    public abstract Constraint Negate(NielsenContext ctx);
}