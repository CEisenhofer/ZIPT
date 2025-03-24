using Microsoft.Z3;
using StringBreaker.Constraints;
using StringBreaker.Constraints.ConstraintElement;
using StringBreaker.Tokens;

namespace StringBreaker.IntUtils;

public abstract class NonTermInt : IComparable<NonTermInt> {
    public abstract Poly Apply(Subst subst);
    public abstract Poly Apply(Interpretation subst);
    public abstract int CompareToInternal(NonTermInt other);
    public int CompareTo(NonTermInt? other) {
        if (other is null)
            return 1;
        if (ReferenceEquals(other, this))
            return 0;
        int cmp = GetType().TypeHandle.Value.CompareTo(other.GetType().TypeHandle.Value);
        return cmp != 0 ? cmp : CompareToInternal(other);
    }
    public abstract void CollectSymbols(HashSet<NamedStrToken> vars, HashSet<SymCharToken> sChars, HashSet<IntVar> iVars, HashSet<CharToken> alphabet);
    public abstract IntExpr ToExpr(NielsenGraph graph);
    public abstract override string ToString();
}