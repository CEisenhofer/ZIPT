using System.Diagnostics;
using Microsoft.Z3;
using ZIPT.Constraints;
using ZIPT.MiscUtils;
using ZIPT.Tokens;

namespace ZIPT.IntUtils;

// A monomial with factor 1
public class StrictMonomial : MSet<NonTermInt, BigInt> {

    public StrictMonomial() { }

    public StrictMonomial(NonTermInt v) : base(v) { }

    public StrictMonomial(NonTermInt v, BigInt coeff) : base(v, coeff) { }

    public StrictMonomial(StrictMonomial other) : base(other) { }

    public Interval GetBounds(NielsenNode node) {
        Interval res = new(1);
        foreach (var c in this) {
            if (!node.IntBounds.TryGetValue(c.t, out var bounds)) {
                if (c.t is LenVar)
                    bounds = new Interval(0, BigIntInf.PosInf);
                else
                    return Interval.Full;
            }
            Interval curr = new BigIntInf(c.occ) * bounds;
            res = res.MergeMultiplication(curr);
            if (res.IsFull)
                return res;
        }
        return res;
    }

    public new StrictMonomial Clone() => new(this);

    public IntPoly Apply(Subst subst) {
        IntPoly result = new(BigInt.One);
        foreach (var c in this) {
            Debug.Assert(c.occ.IsPos);
            var b = c.t.Apply(subst);
            var p = b;
            for (BigInt i = 1; i < c.occ; i += BigInt.One) {
                p = IntPoly.Mul(p, b);
            }
            result = IntPoly.Mul(result, p);
        }
        return result;
    }

    public IntPoly Apply(Interpretation subst) {
        IntPoly result = new(BigInt.One);
        foreach (var c in this) {
            Debug.Assert(c.occ.IsPos);
            var b = c.t.Apply(subst);
            var p = b;
            for (BigInt i = 1; i < c.occ; i += BigInt.One) {
                p = IntPoly.Mul(p, b);
            }
            result = IntPoly.Mul(result, p);
        }
        return result;
    }

    public (BigInt coeff, StrictMonomial monomial) Simplify(NielsenNode node) {
        StrictMonomial mon = new();
        BigInt coeff = BigInt.One;
        foreach (var c in this) {
            if (node.IntBounds.TryGetValue(c.t, out var val) && val is { IsUnit: true, Min.IsInf: false }) {
                for (BigInt i = 0; i < c.occ; i += BigInt.One) {
                    coeff *= (BigInt)val.Min;
                }
            }
            else
                mon.Add(c.t, c.occ);
        }
        return (coeff, mon);
    }

    public RatPoly Apply(NonTermInt v, RatPoly expressed) =>
        Apply(new Dictionary<NonTermInt, RatPoly> { { v, expressed } });

    public RatPoly Apply(Dictionary<NonTermInt, RatPoly> intSubst) {
        RatPoly result = new(BigRat.One);
        foreach (var c in this) {
            Debug.Assert(c.occ.IsPos);
            RatPoly p;
            if (intSubst.TryGetValue(c.t, out var b)) {
                p = b;
                for (int i = 1; i < c.occ; i++) {
                    p = RatPoly.Mul(p, b);
                }
            }
            else
                p = new RatPoly(new StrictMonomial(c.t, c.occ));
            result = RatPoly.Mul(result, p);
        }
        return result;
    }

    public void CollectSymbols(NonTermSet nonTermSet, HashSet<CharToken> alphabet) {
        foreach (var c in this) {
            c.t.CollectSymbols(nonTermSet, alphabet);
        }
    }

    public IntExpr ToExpr(NielsenGraph graph) {
        if (IsEmpty())
            return graph.Ctx.MkInt(1);
        IntExpr result = graph.Ctx.MkInt(1);
        foreach (var c in this) {
            Debug.Assert(c.occ > 0);
            var b = c.t.ToExpr(graph);
            for (int i = 0; i < c.occ; i++) {
                result = (IntExpr)graph.Ctx.MkMul(result, b);
            }
        }
        return result;
    }

    public override string ToString() =>
        IsEmpty() ? "1" : string.Concat(this.Select(o =>
        {
            Debug.Assert(o.occ > 0);
            if (o.occ == 1)
                return o.t.ToString();
            string occStr = o.occ.ToString();
            return occStr.Length == 1 ? o.t + "^" + occStr : o.t + "^{" + occStr + "}";
        }));

}