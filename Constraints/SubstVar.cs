using StringBreaker.Tokens;

namespace StringBreaker.Constraints;

public class SubstVar : Subst {

    public StrVarToken Var { get; }
    public Str Str { get; }

    public override bool IsEliminating => !Str.RecursiveIn(Var);

    public SubstVar(StrVarToken v) {
        Var = v;
        Str = [];
    }

    public SubstVar(StrVarToken v, Str s) {
        Var = v;
        Str = s;
    }

    public override Str ResolveVar(StrVarToken v) => v.Equals(Var) ? Str : [v];
    public override Str ResolveVar(SymCharToken v) => [v];
    public override void AddToInterpretation(Interpretation itp) => itp.Add(this);

    public override string ToString() => $"{Var} / {Str}";

    public override bool Equals(object? obj) =>
        obj is SubstVar substitution && Equals(substitution);

    public bool Equals(SubstVar subst) => Var.Equals(subst.Var) && Str.Equals(subst.Str);
    public override int GetHashCode() => HashCode.Combine(Var, Str);
}