using System.ComponentModel;
using Microsoft.Z3;
using StringBreaker.Tokens;

namespace StringBreaker.Constraints;

public abstract class Subst {

    public abstract bool IsEliminating { get; }

    public abstract Str ResolveVar(NamedStrToken v);
    public abstract Str ResolveVar(SymCharToken v);

    public abstract void AddToInterpretation(Interpretation itp);

    public abstract Expr KeyExpr(NielsenGraph graph);
    public abstract Expr ValueExpr(NielsenGraph graph);
    public abstract IntExpr KeyLenExpr(NielsenGraph graph);
    public abstract IntExpr ValueLenExpr(NielsenGraph graph);
    public abstract bool EqualKeys(Subst subst);
    public abstract override string ToString();

    public abstract override bool Equals(object? obj);
    public abstract override int GetHashCode();
}