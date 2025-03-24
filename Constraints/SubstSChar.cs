using System.Diagnostics;
using Microsoft.Z3;
using StringBreaker.Tokens;

namespace StringBreaker.Constraints;

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

    public override Expr KeyExpr(NielsenGraph graph) => Sym.ToExpr(graph);
    public override Expr ValueExpr(NielsenGraph graph) => C.ToExpr(graph);

    public override string ToString() => $"{Sym} / {C}";

    public override bool Equals(object? obj) =>
        obj is SubstSChar substitution && Equals(substitution);

    public bool Equals(SubstSChar subst) => Sym.Equals(subst.Sym) && C.Equals(subst.C);
    public override int GetHashCode() => HashCode.Combine(Sym, C);
}