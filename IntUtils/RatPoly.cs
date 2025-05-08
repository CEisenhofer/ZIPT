using StringBreaker.Constraints;
using StringBreaker.MiscUtils;
using StringBreaker.Tokens;

namespace StringBreaker.IntUtils;

public class RatPoly : Poly<BigRat, RatPoly> {

    public RatPoly() { }

    public RatPoly(BigRat l) {
        StrictMonomial constMonomial = new();
        Add(constMonomial, l);
    }

    public RatPoly(NonTermInt v) : base(new StrictMonomial(v)) { }

    public RatPoly(StrictMonomial s) : base(s) { }

    public RatPoly(MSet<StrictMonomial, BigRat> s) : base(s) { }

    public new RatPoly Clone() {
        RatPoly poly = new();
        foreach (var c in this) {
            poly.Add(new StrictMonomial(c.t), c.occ);
        }
        return poly;
    }

    public RatPoly Apply(NonTermInt bestVar, RatPoly expressed) {
        RatPoly ret = new();
        foreach (var c in this) {
            RatPoly p = c.t.Apply(bestVar, expressed);
            p = Mul(p, new RatPoly(c.occ));
            ret.Plus(p);
        }
        return ret;
    }

    public void CollectSymbols(NonTermSet nonTermSet, HashSet<CharToken> alphabet) {
        foreach (var c in this) {
            c.t.CollectSymbols(nonTermSet, alphabet);
        }
    }

}