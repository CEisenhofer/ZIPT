using Microsoft.Z3;
using ZIPT.IntUtils;
using ZIPT.Tokens;

namespace ZIPT.Constraints;

public class SubstVar : Subst {

    public NamedStrToken Var { get; }
    public IStr IStr { get; }

    public override bool IsEliminating => !IStr.RecursiveIn(Var);

    public SubstVar(NamedStrToken v) {
        Var = v;
        IStr = [];
    }

    public SubstVar(NamedStrToken v, IStr s) {
        Var = v;
        IStr = s;
    }

    public override IStr ResolveVar(NamedStrToken v) => v.Equals(Var) ? IStr : [v];
    public override IStr ResolveVar(SymCharToken v) => [v];
    public override void AddToInterpretation(Interpretation itp) => itp.Add(this);

    public override Expr KeyExpr(NielsenGraph graph) => Var.ToExpr(graph);
    public override Expr ValueExpr(NielsenGraph graph) => IStr.ToExpr(graph);
    public override IntExpr KeyLenExpr(NielsenGraph graph) => LenVar.MkLenPoly([Var]).ToExpr(graph);
    public override IntExpr ValueLenExpr(NielsenGraph graph) => LenVar.MkLenPoly(IStr).ToExpr(graph);
    public override void CollectValueSymbols(NonTermSet nonTermSet) => IStr.CollectSymbols(nonTermSet, []);

    public override bool EqualKeys(Subst subst) => 
        subst is SubstVar substitution && Var.Equals(substitution.Var);

    public override string ToString() => $"{Var} / {IStr}";

    public override bool Equals(object? obj) =>
        obj is SubstVar substitution && Equals(substitution);

    public bool Equals(SubstVar subst) => Var.Equals(subst.Var) && IStr.Equals(subst.IStr);
    public override int GetHashCode() => HashCode.Combine(Var, IStr);
}