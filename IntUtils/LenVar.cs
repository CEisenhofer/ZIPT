using Microsoft.Z3;
using StringBreaker.Constraints;
using StringBreaker.Tokens;

namespace StringBreaker.IntUtils;

public sealed class LenVar : StrDepIntVar {

    public LenVar(NamedStrToken v) : base(v) {}

    public override bool Equals(object? obj) => obj is LenVar var && Equals(var);
    public bool Equals(LenVar other) => Var.Equals(other.Var);

    public override int GetHashCode() => Var.GetHashCode() * 416749777;

    public override IntPoly Apply(Subst subst) => 
        MkLenPoly(subst.ResolveVar(Var));
    public override IntPoly Apply(Interpretation subst) =>
        MkLenPoly(subst.ResolveVar(Var));

    public static IntPoly MkLenPoly(Str s) {
        IntPoly poly = new();
        foreach (var t in s) {
            switch (t) {
                case UnitToken:
                    poly.Plus(1);
                    break;
                case NamedStrToken v:
                    poly.Plus(new IntPoly(new LenVar(v)));
                    break;
                case PowerToken pt:
                {
                    var subPoly = MkLenPoly(pt.Base);
                    poly.Plus(IntPoly.Mul(subPoly, pt.Power));
                    break;
                }
                default:
                    throw new NotSupportedException();
            }
        }
        return poly;
    }

    public override int CompareToInternal(NonTermInt other) =>
        Var.CompareTo(((LenVar)other).Var);

    public override void CollectSymbols(NonTermSet nonTermSet, HashSet<CharToken> alphabet) => nonTermSet.Add(Var);

    public override IntExpr ToExpr(NielsenGraph graph) {
        IntExpr? e = graph.Cache.GetCachedIntExpr(this, graph);
        if (e is not null)
            return e;

        e = (IntExpr)graph.Ctx.MkFreshConst("len_" + Var, graph.Ctx.IntSort);
        graph.Cache.SetCachedExpr(this, e, graph);
        return e;
    }

    public override string ToString() => $"|{Var}|";
}