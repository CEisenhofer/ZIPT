using Microsoft.Z3;
using StringBreaker.Constraints;
using StringBreaker.Constraints.ConstraintElement;
using StringBreaker.Tokens;

namespace StringBreaker.IntUtils;

public class Ite : NonTermInt {

    public Constraint Cond { get; }
    public Poly Then { get; }
    public Poly Els { get; }

    public override Len MinLen => Len.NegInf;

    public Ite(Constraint cond, Poly then, Poly els) {
        Cond = cond;
        Then = then;
        Els = els;
    }

    public override Poly Apply(Subst subst) {
        var c = Cond.Clone();
        var t = Then.Clone();
        var e = Els.Clone();
        c.Apply(subst);
        t.Apply(subst);
        e.Apply(subst);
        return new Poly(new StrictMonomial(new Ite(c, t, e)));
    }

    public override Poly Apply(Interpretation subst) {
        var c = Cond.Clone();
        var t = Then.Clone();
        var e = Els.Clone();
        c.Apply(subst);
        t.Apply(subst);
        e.Apply(subst);
        return new Poly(new StrictMonomial(new Ite(c, t, e)));
    }

    public override int CompareToInternal(NonTermInt other) {
        int cmp;
        if (Cond.GetType() == other.GetType()) {
            if (Cond is IntConstraint ic)
                cmp = ic.CompareTo((IntConstraint)((Ite)other).Cond);
            else
                cmp = ((StrConstraint)Cond).CompareTo((StrConstraint)((Ite)other).Cond);
        }
        else 
            return Cond.GetType().TypeHandle.Value.CompareTo(other.GetType().TypeHandle.Value);
        if (cmp != 0)
            return cmp;
        cmp = Then.CompareTo(((Ite)other).Then);
        return cmp != 0 ? cmp : Els.CompareTo(((Ite)other).Els);
    }

    public override void CollectSymbols(HashSet<NamedStrToken> vars, HashSet<SymCharToken> sChars, 
        HashSet<IntVar> iVars, HashSet<CharToken> alphabet) {
        Cond.CollectSymbols(vars, sChars, iVars, alphabet);
        Then.CollectSymbols(vars, sChars, iVars, alphabet);
        Els.CollectSymbols(vars, sChars, iVars, alphabet);
    }

    public override IntExpr ToExpr(NielsenGraph graph) =>
        (IntExpr)graph.Ctx.MkITE(
            Cond.ToExpr(graph),
            Then.ToExpr(graph),
            Els.ToExpr(graph)
        );

    public override string ToString() => 
        $"ite({Cond}, {Then}, {Els})";
}