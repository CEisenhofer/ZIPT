using Microsoft.Z3;
using StringBreaker.Constraints;
using StringBreaker.MiscUtils;
using StringBreaker.Tokens;

namespace StringBreaker.IntUtils;

public class IntPoly : Poly<BigInt, IntPoly> {

    public IntPoly() { }

    public IntPoly(BigInt l) {
        StrictMonomial constMonomial = new();
        Add(constMonomial, l);
    }

    public IntPoly(NonTermInt v) : base(new StrictMonomial(v)) { }

    public IntPoly(StrictMonomial s) : base(s) { }

    public IntPoly(MSet<StrictMonomial, BigInt> s) : base(s) { }

    public Interval GetBounds(NielsenNode node) => 
        GetBounds(node, this);

    public static Interval GetBounds(NielsenNode node, IEnumerable<(StrictMonomial t, BigInt occ)> monomials) {
        Interval res = new();
        foreach (var c in monomials) {
            Interval curr = new BigIntInf(c.occ) * c.t.GetBounds(node);
            res = res.MergeAddition(curr);
            if (res.IsFull)
                return res;
        }
        return res;
    }

    public new IntPoly Clone() {
        IntPoly poly = new();
        foreach (var c in this) {
            poly.Add(new StrictMonomial(c.t), c.occ);
        }
        return poly;
    }

    public IntPoly Apply(Subst subst) {
        IntPoly ret = new();
        foreach (var c in this) {
            IntPoly p = c.t.Apply(subst);
            p = Mul(p, new IntPoly(c.occ));
            ret.Plus(p);
        }
        return ret;
    }

    public IntPoly Apply(Interpretation subst) {
        IntPoly ret = new();
        foreach (var c in this) {
            IntPoly p = c.t.Apply(subst);
            p = Mul(p, new IntPoly(c.occ));
            ret.Plus(p);
        }
        return ret;
    }

    public RatPoly Apply(Dictionary<NonTermInt, RatPoly> intSubst) {
        RatPoly ret = new();
        foreach (var c in this) {
            RatPoly p = c.t.Apply(intSubst);
            p = RatPoly.Mul(p, new RatPoly(new BigRat(c.occ)));
            ret.Plus(p);
        }
        return ret;
    }

    public IntPoly Simplify(NielsenNode node) {
        IntPoly ret = new();
        foreach (var m in this) {
            var p = m.t.Simplify(node);
            ret.Add(p.monomial, p.coeff * m.occ);
        }
        return ret;
    }

    public void CollectSymbols(NonTermSet nonTermSet, HashSet<CharToken> alphabet) {
        foreach (var c in this) {
            c.t.CollectSymbols(nonTermSet, alphabet);
        }
    }

    public RatPoly ToRatPoly() {
        RatPoly ret = new();
        foreach (var c in this) {
            ret.Add(c.t, new BigRat(c.occ));
        }
        return ret;
    }

    public IntExpr ToExpr(NielsenGraph graph) {
        if (IsEmpty())
            return graph.Ctx.MkInt(0);
        return (IntExpr)graph.Ctx.MkAdd(this.Select(o => graph.Ctx.MkMul(o.occ.ToExpr(graph), o.t.ToExpr(graph))).ToArray());
    }
}