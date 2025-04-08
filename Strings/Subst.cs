using System.ComponentModel;
using Microsoft.Z3;
using StringBreaker.Constraints;
using StringBreaker.Strings.Tokens;

namespace StringBreaker.Strings;

public abstract class Subst {

    public abstract bool IsEliminating { get; }

    public abstract Str ResolveVar(NamedStrToken v);
    public abstract Str ResolveVar(SymCharToken v);

    public abstract void AddToInterpretation(Interpretation itp);

    public abstract Expr KeyExpr(NielsenContext ctx);
    public abstract Expr ValueExpr(NielsenContext ctx);
    public abstract IntExpr KeyLenExpr(NielsenContext ctx);
    public abstract IntExpr ValueLenExpr(NielsenContext ctx);
    public abstract override string ToString();

    public abstract override bool Equals(object? obj);
    public abstract override int GetHashCode();
}