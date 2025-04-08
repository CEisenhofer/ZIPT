using System.Diagnostics;
using Microsoft.Z3;
using StringBreaker.Constraints;
using StringBreaker.MiscUtils;
using StringBreaker.Strings;
using StringBreaker.Strings.Tokens;

namespace StringBreaker.IntUtils;

// A monomial with factor 1
public class StrictMonomial : MSet<NonTermInt> {

    public StrictMonomial() { }

    public StrictMonomial(NonTermInt v) : base(v) { }

    public StrictMonomial(StrictMonomial other) : base(other) { }

    public Interval GetBounds(NielsenNode node) {
        Interval res = new(1);
        foreach (var c in this) {
            if (!node.IntBounds.TryGetValue(c.t, out var bounds)) {
                if (c.t is LenVar)
                    bounds = new Interval(0, Len.PosInf);
                else
                    return Interval.Full;
            }
            Interval curr = c.occ * bounds;
            res = res.MergeMultiplication(curr);
            if (res.IsFull)
                return res;
        }
        return res;
    }

    public new StrictMonomial Clone() => new(this);

    public Poly Apply(Subst subst) {
        Poly result = new(1);
        foreach (var c in this) {
            Debug.Assert(c.occ > 0);
            var b = c.t.Apply(subst);
            var p = b;
            for (int i = 1; i < c.occ; i++) {
                p = Poly.Mul(p, b);
            }
            result = Poly.Mul(result, p);
        }
        return result;
    }

    public Poly Apply(Interpretation subst) {
        Poly result = new(1);
        foreach (var c in this) {
            Debug.Assert(c.occ > 0);
            var b = c.t.Apply(subst);
            var p = b;
            for (int i = 1; i < c.occ; i++) {
                p = Poly.Mul(p, b);
            }
            result = Poly.Mul(result, p);
        }
        return result;
    }

    public (Len coeff, StrictMonomial monomial) Simplify(NielsenNode node) {
        StrictMonomial mon = new();
        Len coeff = 1;
        foreach (var c in this) {
            if (node.IntBounds.TryGetValue(c.t, out var val) && val.IsUnit) {
                for (int i = 0; i < c.occ; i++) {
                    coeff *= val.Min;
                }
            }
            else
                mon.Add(c.t, c.occ);
        }
        return (coeff, mon);
    }

    public void CollectSymbols(HashSet<NamedStrToken> vars, HashSet<SymCharToken> sChars, 
        HashSet<IntVar> iVars, HashSet<CharToken> alphabet) {

        foreach (var c in this) {
            c.t.CollectSymbols(vars, sChars, iVars, alphabet);
        }
    }

    public IntExpr ToExpr(NielsenContext ctx) {
        if (IsEmpty())
            return ctx.Graph.Ctx.MkInt(1);
        IntExpr result = ctx.Graph.Ctx.MkInt(1);
        foreach (var c in this) {
            Debug.Assert(c.occ > 0);
            var b = c.t.ToExpr(ctx);
            for (int i = 0; i < c.occ; i++) {
                result = (IntExpr)ctx.Graph.Ctx.MkMul(result, b);
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