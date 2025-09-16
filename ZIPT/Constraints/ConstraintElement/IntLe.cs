using Microsoft.Z3;
using System.Diagnostics;
using System.Numerics;
using ZIPT.Constraints.Modifier;
using ZIPT.IntUtils;
using ZIPT.Strings;
using ZIPT.Strings.Tokens;

namespace ZIPT.Constraints.ConstraintElement;

// Poly <= 0
public class IntLe : IntConstraint {

    public PDD<BigInteger> Poly { get; set; }

    public IntLe(PDD<BigInteger> poly) => Poly = poly;

    // rhs does not need to be cloned
    public IntLe(PDD<BigInteger> lhs, PDD<BigInteger> rhs) => 
        Poly = lhs.Sub(rhs);

    // rhs does not need to be cloned
    public static IntLe MkLt(PDD<BigInteger> lhs, PDD<BigInteger> rhs) {
        var ret = new IntLe(lhs, rhs);
        ret.Poly = ret.Poly.Add(lhs.One);
        return ret;
    }

    // rhs does not need to be cloned
    public static IntLe MkLe(PDD<BigInteger> lhs, PDD<BigInteger> rhs) => new(lhs, rhs);

    public override IntLe Apply(Subst subst, NielsenNode node) {
        var (oldLen, newLen) = subst.GetLenReplacement(node.Env);
        var n = Poly.Substitute(oldLen, newLen);
        return ReferenceEquals(Poly, n) ? this : new IntLe(n);
    }

    public override IntLe Apply(Interpretation itp) {
        var n = Poly;
        foreach (var kv in itp.IntVal) {
            n = n.Substitute(kv.Key, itp.Env.IntPDDManager.MkPDD(kv.Value));
        }
        return ReferenceEquals(Poly, n) ? this : new IntLe(n);
    }

    public override bool Equals(object? obj) =>
        obj is IntLe le && Equals(le);

    public bool Equals(IntLe other) =>
        Poly.Equals(other.Poly);

    public override int GetHashCode() =>
        Poly.GetHashCode();

    public override string ToString() {
        var (pos, neg) = Poly.GetPosNeg();
        return $"{pos} \u2264 {neg}";
    }

    public SimplifyResult Simplify(NielsenNode node) {
        if (Poly.IsConst(out BigInteger val))
            return val <= 0 ? SimplifyResult.Satisfied : SimplifyResult.Conflict;
        var bounds = Poly.GetBounds(node);
        if (!bounds.Max.IsPos)
            return SimplifyResult.Satisfied;
        if (bounds.Min.IsPos)
            return SimplifyResult.Conflict;
        var (monomials, offset) = Poly.MonomialDecomposition();
        BigInteger gcd = BigInteger.Abs(monomials.First().Coefficient);
        Debug.Assert(gcd.Sign > 0);
        if (gcd.IsOne) 
            return SimplifyResult.Proceed;
        foreach (var occ in monomials.Skip(1)) {
            gcd = BigInteger.GreatestCommonDivisor(gcd, occ.Coefficient);
            Debug.Assert(!gcd.IsZero);
            if (gcd.Equals(1))
                break;
        }
        Debug.Assert(gcd.Sign > 0);
        if (gcd.IsOne) 
            return SimplifyResult.Proceed;
        var newPoly = Poly.Zero;
        foreach (var p in monomials) {
            Debug.Assert(p.Variables.Count == 0 || BigInteger.DivRem(p.Coefficient, gcd).Remainder.IsZero);
            newPoly = newPoly.Add(
                new PDD<BigInteger>.Monomial(
                    BigInteger.Divide(p.Coefficient, gcd), p.Variables).ToPDD(node.Env.IntPDDManager)
            );
        }
        if (!offset.IsZero) {
            if (offset.Sign > 0) {
                var (r, m) = BigInteger.DivRem(offset, gcd);
                newPoly = newPoly.Add(m.IsZero ? r : r + 1) ;
            }
            else
                newPoly = newPoly.Add(BigInteger.Divide(offset, gcd));
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

        var (monomials, _) = Poly.MonomialDecomposition();

        foreach (var n in monomials) {
            if (n.Variables.Count == 0) {
                Debug.Assert(false);
                // Ignored - constant offset
                i++;
                continue;
            }
            if (n.Variables.Count != 1) {
                // Not linear (x...y)
                i++;
                continue;
            }
            var r = n.Variables[0];
            if (r.Pow != 1) {
                // Some power (x^n with n != 1)
                i++;
                continue;
            }
            int i0 = i++;
            var lb = PDD<BigInteger>.GetBounds(node, monomials.Where((_, j) => i0 != j));
            bool isHigh = n.Coefficient.Sign > 0;
            if (isHigh)
                lb = lb.Negate();
            lb /= BigInteger.Abs(n.Coefficient);
            switch (isHigh
                        ? node.AddHigherIntBound(r.Var, lb.Max)
                        : node.AddLowerIntBound(r.Var, lb.Min)) {
                case SimplifyResult.Conflict:
                    reason = BacktrackReasons.Arithmetic;
                    return SimplifyResult.Conflict;
                case SimplifyResult.Restart:
                    restart = true;
                    break;
            }
        }
        return restart ? SimplifyResult.Restart : SimplifyResult.Proceed;
    }

    public override BoolExpr ToExpr(NielsenGraph graph) =>
        graph.Ctx.MkLe(Poly.ToExpr(graph), graph.Ctx.MkInt(0));
    
    public override void CollectSymbols(NonTermSet nonTermSet,  HashSet<CharToken> alphabet) =>
        Poly.CollectSymbols(nonTermSet, alphabet);

    public override IntConstraint Negate() =>
        MkLt(Poly.Zero, Poly);

    public override int CompareToInternal(IntConstraint other) =>
        Poly.CompareTo(((IntLe)other).Poly);
}