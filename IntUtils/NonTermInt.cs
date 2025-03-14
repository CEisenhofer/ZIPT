using Microsoft.Z3;
using StringBreaker.Constraints;
using StringBreaker.Tokens;

namespace StringBreaker.IntUtils;

public abstract class NonTermInt : IComparable<NonTermInt> {
    public abstract Poly Apply(Subst subst);
    public abstract Poly Apply(Interpretation subst);
    public abstract int CompareTo(NonTermInt? other);
    public abstract void CollectSymbols(HashSet<StrVarToken> vars, HashSet<CharToken> alphabet);
    public abstract IntExpr ToExpr(NielsenGraph graph);
    public abstract override string ToString();
}