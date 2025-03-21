using System.ComponentModel;
using StringBreaker.Tokens;

namespace StringBreaker.Constraints;

public abstract class Subst {

    public abstract bool IsEliminating { get; }

    public abstract Str ResolveVar(StrVarToken v);
    public abstract Str ResolveVar(SymCharToken v);

    public abstract void AddToInterpretation(Interpretation itp);

    public abstract override string ToString();

    public abstract override bool Equals(object? obj);
    public abstract override int GetHashCode();
}