using Microsoft.Z3;
using StringBreaker.Constraints;
using StringBreaker.Tokens;

namespace StringBreaker.IntUtils;

public class LenVar : NonTermInt {

    StrVarToken Var { get; }

    public LenVar(StrVarToken v) =>
        Var = v;

    public override bool Equals(object? obj) => obj is LenVar var && Equals(var);
    public bool Equals(LenVar other) => Var.Equals(other.Var);

    public override int GetHashCode() => Var.GetHashCode() * 416749777;
    public override Poly Apply(Subst subst) => 
        MkLenPoly(subst.ResolveVar(Var));
    public override Poly Apply(Interpretation subst) =>
        MkLenPoly(subst.ResolveVar(Var));

    public static Poly MkLenPoly(Str s) {
        Poly poly = new();
        foreach (var t in s) {
            switch (t) {
                case CharToken:
                    poly.AddPoly(new Poly(1));
                    break;
                case StrVarToken v:
                    poly.AddPoly(new Poly(new LenVar(v)));
                    break;
                case PowerToken pt:
                {
                    var subPoly = MkLenPoly(pt.Base);
                    poly.AddPoly(Poly.MulPoly(subPoly, pt.Power));
                    break;
                }
                default:
                    throw new NotSupportedException();
            }
        }
        return poly;
    }

    public override int CompareTo(NonTermInt? other) {
        if (other is LenVar len)
            return Var.CompareTo(len.Var);
        return 0;
    }

    public override void CollectSymbols(HashSet<StrVarToken> vars, HashSet<CharToken> alphabet) => vars.Add(Var);

    public override IntExpr ToExpr(NielsenGraph graph) => 
        graph.Propagator.MkLen(Var.ToExpr(graph));

    public override string ToString() => $"|{Var}|";
}