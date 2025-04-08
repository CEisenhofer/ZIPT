using System.Diagnostics;
using Microsoft.Z3;
using StringBreaker.Constraints;
using StringBreaker.Strings.Tokens;

namespace StringBreaker.Strings;

public class SubstSChar : Subst {

    public SymCharToken Sym { get; }
    public UnitToken C { get; }

    public override bool IsEliminating => !C.Equals(Sym);

    public SubstSChar(SymCharToken v, UnitToken c) {
        Sym = v;
        C = c;
        Debug.Assert(!v.Equals(c));
    }

    public override Str ResolveVar(NamedStrToken v) => [v];
    public override Str ResolveVar(SymCharToken v) => v.Equals(Sym) ? [C] : [v];
    public override void AddToInterpretation(Interpretation itp) => itp.Add(this);

    public override Expr KeyExpr(NielsenContext ctx) => Sym.ToExpr(ctx);
    public override Expr ValueExpr(NielsenContext ctx) => C.ToExpr(ctx);
    public override IntExpr KeyLenExpr(NielsenContext ctx) => ctx.Graph.Ctx.MkInt(1);
    public override IntExpr ValueLenExpr(NielsenContext ctx) => ctx.Graph.Ctx.MkInt(1);

    public override string ToString() => $"{Sym} / {C}";

    public override bool Equals(object? obj) =>
        obj is SubstSChar substitution && Equals(substitution);

    public bool Equals(SubstSChar subst) => Sym.Equals(subst.Sym) && C.Equals(subst.C);
    public override int GetHashCode() => HashCode.Combine(Sym, C);
}