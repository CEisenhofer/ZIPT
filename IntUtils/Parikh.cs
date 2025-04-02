using Microsoft.Z3;
using StringBreaker.Constraints;
using StringBreaker.Constraints.ConstraintElement;
using StringBreaker.Tokens;

namespace StringBreaker.IntUtils;

public class Parikh : StrDepIntVar {

    public CharToken Sym { get; }

    public Parikh(CharToken c, StrVarToken v) : base(v) => Sym = c;

    public override bool Equals(object? obj) => obj is Parikh var && Equals(var);
    public bool Equals(Parikh other) => Var.Equals(other.Var) && Sym.Equals(other.Sym);

    public override int GetHashCode() => HashCode.Combine(Var, Sym);
    public override Poly Apply(Subst subst) =>
        MkParikhPoly(Sym, subst.ResolveVar(Var));
    public override Poly Apply(Interpretation subst) =>
        MkParikhPoly(Sym, subst.ResolveVar(Var));

    public static Poly MkParikhPoly(CharToken sym, Str s) {
        Poly poly = new();
        foreach (var t in s) {
            switch (t) {
                case CharToken c:
                    if (c.Equals(sym))
                        poly.Plus(1);
                    break;
                case SymCharToken sc:
                    poly.Plus(new Poly(new Ite(new StrEq([sc], [sym]), new Poly(1), new Poly(0))));
                    break;
                case StrVarToken v:
                    poly.Plus(new Poly(new Parikh(sym, v)));
                    break;
                case PowerToken pt:
                    poly.Plus(Poly.Mul(MkParikhPoly(sym, pt.Base), pt.Power));
                    break;
                default:
                    throw new NotSupportedException();
            }
        }
        return poly;
    }

    public override int CompareToInternal(NonTermInt other) {
        int cmp = Sym.CompareTo(((Parikh)other).Sym);
        return cmp != 0 ? cmp : Var.CompareTo(((Parikh)other).Var);
    }

    public override void CollectSymbols(HashSet<NamedStrToken> vars, HashSet<SymCharToken> sChars, 
        HashSet<IntVar> iVars,
        HashSet<CharToken> alphabet) {
        vars.Add(Var);
        alphabet.Add(Sym);
    }

    public override IntExpr ToExpr(NielsenGraph graph) => 
        graph.Cache.MkParikh(Sym, Var.ToExpr(graph));

    public override string ToString() => $"|{Var}|[{Sym}]";
}