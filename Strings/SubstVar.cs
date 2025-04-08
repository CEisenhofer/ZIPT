using System.Diagnostics;
using Microsoft.Z3;
using StringBreaker.Constraints;
using StringBreaker.IntUtils;
using StringBreaker.Strings.Tokens;

namespace StringBreaker.Strings;

public class SubstVar : Subst {

    public StrTokenRef Var { get; }
    public NamedStrToken VarToken => (NamedStrToken)Var.Token;
    public Str Str { get; }

    public override bool IsEliminating => !Str.RecursiveIn(Var);

    public SubstVar(StrTokenRef v) {
        Debug.Assert(v.Token is NamedStrToken);
        Var = v;
        Str = [];
    }

    public SubstVar(StrTokenRef v, Str s) {
        Debug.Assert(v.Token is NamedStrToken);
        Var = v;
        Str = s;
    }

    public override StrRef ResolveVar(NamedStrToken v) => v.Equals(Var) ? Str : [v];
    public override StrRef ResolveVar(SymCharToken v) => [v];
    public override void AddToInterpretation(Interpretation itp) => itp.Add(this);

    public override Expr KeyExpr(NielsenContext ctx) => Var.ToExpr(ctx);
    public override Expr ValueExpr(NielsenContext ctx) => Str.ToExpr(ctx);
    public override IntExpr KeyLenExpr(NielsenContext ctx) => LenVar.MkLenPoly([Var]).ToExpr(ctx);
    public override IntExpr ValueLenExpr(NielsenContext ctx) => LenVar.MkLenPoly(Str).ToExpr(ctx);

    public override string ToString() => $"{Var} / {Str}";

    public override bool Equals(object? obj) =>
        obj is SubstVar substitution && Equals(substitution);

    public bool Equals(SubstVar subst) => Var.Equals(subst.Var) && Str.Equals(subst.Str);
    public override int GetHashCode() => HashCode.Combine(Var, Str);
}