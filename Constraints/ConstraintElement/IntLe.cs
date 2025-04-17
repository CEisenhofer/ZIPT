using Microsoft.Z3;
using StringBreaker.Constraints.Modifier;
using StringBreaker.IntUtils;
using StringBreaker.Tokens;
using System.Diagnostics;
using System.Numerics;

namespace StringBreaker.Constraints.ConstraintElement;

// Poly <= 0
public class IntLe : IntConstraint {

    public Poly Poly { get; set; }

    public IntLe(Poly poly) => Poly = poly;

    // rhs does not need to be cloned
    public IntLe(Poly lhs, Poly rhs) {
        lhs.Sub(rhs);
        Poly = lhs;
    }

    // rhs does not need to be cloned
    public static IntLe MkLt(Poly lhs, Poly rhs) {
        var ret = new IntLe(lhs.Clone(), rhs);
        ret.Poly.Plus(1);
        return ret;
    }

    // rhs does not need to be cloned
    public static IntLe MkLe(Poly lhs, Poly rhs) => new(lhs, rhs);

    public override IntLe Clone() => new(Poly.Clone());

    public override bool Equals(object? obj) =>
        obj is IntLe le && Equals(le);

    public bool Equals(IntLe other) =>
        Poly.Equals(other.Poly);

    public override int GetHashCode() =>
        Poly.GetHashCode();

    public override string ToString() {
        Poly.GetPosNeg(out var pos, out var neg);
        return $"{pos} \u2264 {neg}";
    }

    public override void Apply(Subst subst) => Poly = Poly.Apply(subst);
    public override void Apply(Interpretation itp) => Poly = Poly.Apply(itp);

    public SimplifyResult Simplify(NielsenNode node) {
        Poly = Poly.Simplify(node);
        if (Poly.IsConst(out Len val))
            return val <= 0 ? SimplifyResult.Satisfied : SimplifyResult.Conflict;
        var bounds = Poly.GetBounds(node);
        if (!bounds.Max.IsPos)
            return SimplifyResult.Satisfied;
        if (bounds.Min.IsPos)
            return SimplifyResult.Conflict;
        BigInteger gcd = (BigInteger)Poly.NonConst.First().occ.Abs();
        Debug.Assert(gcd.Sign > 0);
        if (gcd.IsOne) 
            return SimplifyResult.Proceed;
        foreach (var occ in Poly.NonConst.Skip(1)) {
            gcd = occ.occ.GreatestCommonDivisor(gcd);
            Debug.Assert(!gcd.IsZero);
            if (gcd.Equals(1))
                break;
        }
        Debug.Assert(gcd.Sign > 0);
        if (gcd.IsOne) 
            return SimplifyResult.Proceed;
        var newPoly = new Poly();
        foreach (var p in Poly.NonConst) {
            Debug.Assert(p.t.IsEmpty() || p.occ.DivRem(gcd).m.IsZero);
            newPoly.Add(p.t, p.occ.Div(gcd));
        }
        var c = Poly.ConstPart;
        if (!c.IsZero) {
            if (c.IsPos) {
                var (r, m) = c.DivRem(gcd);
                if (m.IsZero)
                    newPoly.Add([], r);
                else
                    newPoly.Add([], r + 1);
            }
            else
                newPoly.Add([], c.Div(gcd));
        }
        Poly = newPoly;
        return SimplifyResult.Proceed;
    }

    protected override SimplifyResult SimplifyAndPropagateInternal(NielsenNode node, DetModifier sConstr, ref BacktrackReasons reason) {
        // Simplify
        var res = Simplify(node);
        if (res != SimplifyResult.Proceed) {
            if (res == SimplifyResult.Conflict)
                reason = BacktrackReasons.Arithmetic;
            return res;
        }
        // Propagate bounds
        bool restart = false;
        int i = 0;
        foreach (var n in Poly) {
            if (n.t.IsEmpty()) {
                // Ignored - constant offset
                i++;
                continue;
            }
            if (n.t.Count != 1) {
                // Not linear (x...y)
                i++;
                continue;
            }
            var r = n.t.First();
            if (!r.occ.Equals(1)) {
                // Some power (x^n with n != 1)
                i++;
                continue;
            }
            var lb = Poly.GetBounds(node, Poly.Where((_, j) => i != j));
            bool isHigh = n.occ.IsPos;
            if (isHigh)
                lb = lb.Negate();
            lb /= (BigInteger)n.occ.Abs();
            switch (isHigh
                        ? node.AddHigherIntBound(r.t, lb.Max)
                        : node.AddLowerIntBound(r.t, lb.Min)) {
                case SimplifyResult.Conflict:
                    reason = BacktrackReasons.Arithmetic;
                    return SimplifyResult.Conflict;
                case SimplifyResult.Restart:
                    restart = true;
                    break;
            }

            i++;
        }
        return restart ? SimplifyResult.Restart : SimplifyResult.Proceed;
    }

    public override BoolExpr ToExpr(NielsenGraph graph) =>
        graph.Ctx.MkLe(Poly.ToExpr(graph), graph.Ctx.MkInt(0));
    
    public override void CollectSymbols(HashSet<NamedStrToken> vars, HashSet<SymCharToken> sChars, 
        HashSet<IntVar> iVars, HashSet<CharToken> alphabet) =>
        Poly.CollectSymbols(vars, sChars, iVars, alphabet);

    public override IntConstraint Negate() =>
        MkLt(new Poly(), Poly);

    public override int CompareToInternal(IntConstraint other) =>
        Poly.CompareTo(((IntLe)other).Poly);
}