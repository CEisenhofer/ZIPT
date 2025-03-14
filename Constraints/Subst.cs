using StringBreaker.Tokens;

namespace StringBreaker.Constraints;

public class Subst {

    public StrVarToken Var { get; }
    public Str Str { get; }

    public bool IsEliminating => !Str.RecursiveIn(Var);

    public Subst(StrVarToken v) {
        Var = v;
        Str = [];
    }

    public Subst(StrVarToken v, Str s) {
        Var = v;
        Str = s;
    }

    public Str ResolveVar(StrVarToken v) => v.Equals(Var) ? Str : [v];

    public override string ToString() => $"{Var} / {Str}";

    public override bool Equals(object? obj) =>
        obj is Subst substitution && Equals(substitution);

    public bool Equals(Subst subst) => Var.Equals(subst.Var) && Str.Equals(subst.Str);
    public override int GetHashCode() => HashCode.Combine(Var, Str);
}