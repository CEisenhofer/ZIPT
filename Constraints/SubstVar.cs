using Microsoft.Z3;
using ZIPT.IntUtils;
using ZIPT.Tokens;

namespace ZIPT.Constraints;

public class SubstVar : Subst {

    public NamedStrToken Var { get; }
    public Str Str { get; }

    public override bool IsEliminating => !Str.RecursiveIn(Var);

    public SubstVar(NamedStrToken v) {
        Var = v;
        Str = [];
    }

    public SubstVar(NamedStrToken v, Str s) {
        Var = v;
        Str = s;
    }

    public override Str ResolveVar(NamedStrToken v) => v.Equals(Var) ? Str : [v];
    public override Str ResolveVar(SymCharToken v) => [v];
    public override void AddToInterpretation(Interpretation itp) => itp.Add(this);

    public override Expr KeyExpr(NielsenGraph graph) => Var.ToExpr(graph);
    public override Expr ValueExpr(NielsenGraph graph) => Str.ToExpr(graph);
    public override IntExpr KeyLenExpr(NielsenGraph graph) => LenVar.MkLenPoly([Var]).ToExpr(graph);
    public override IntExpr ValueLenExpr(NielsenGraph graph) => LenVar.MkLenPoly(Str).ToExpr(graph);
    public override bool EqualKeys(Subst subst) => 
        subst is SubstVar substitution && Var.Equals(substitution.Var);

    public override string ToString() => $"{Var} / {Str}";

    public override bool Equals(object? obj) =>
        obj is SubstVar substitution && Equals(substitution);

    public bool Equals(SubstVar subst) => Var.Equals(subst.Var) && Str.Equals(subst.Str);
    public override int GetHashCode() => HashCode.Combine(Var, Str);
}