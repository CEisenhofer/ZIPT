using Microsoft.Z3;
using System.Numerics;
using ZIPT.Constraints.Modifier;
using ZIPT.IntUtils;
using ZIPT.Strings.Tokens;

namespace ZIPT.Constraints.ConstraintElement;

// Poly = R
public class IntEq : IntConstraint {

    public PDD<BigInteger> Poly { get; set; }

    public IntEq(IntEq eq) {
        Poly = eq.Poly;
    }

    public IntEq(PDD<BigInteger> poly) {
        Poly = poly;
        if (!Poly.IsNormal)
            Poly = Poly.Negate();
    }

    public IntEq(PDD<BigInteger> lhs, PDD<BigInteger> rhs) {
        Poly = lhs;
        Poly = Poly.Sub(rhs);
        if (!Poly.IsNormal)
            Poly = Poly.Negate();
    }

    public override IntEq Apply(Subst subst, NielsenNode node) {
        var (oldLen, newLen) = subst.GetLenReplacement(node.Env);
        var n = Poly.Substitute(oldLen, newLen);
        return ReferenceEquals(Poly, n) ? this : new IntEq(n);
    }

    public override Constraint Apply(CharSubst subst, NielsenNode node) => this;

    public override IntEq Apply(Interpretation itp) {
        var n = Poly;
        foreach (var kv in itp.IntVal) {
            n = n.Substitute(kv.Key, itp.Env.IntPDDManager.MkPDD(kv.Value));
        }
        foreach (var kv in itp.Substitution) {
            var (lenVar, newLen) = kv.Value.GetLenReplacement(itp.Env);
            n = n.Substitute(lenVar, newLen);
        }
        return ReferenceEquals(Poly, n) ? this : new IntEq(n);
    }

    public override bool Equals(object? obj) => 
        obj is IntEq eq && Equals(eq);

    public bool Equals(IntEq other) {
        // Poly == other.Poly || Poly == -other.Poly (this is the same => Normalize)
        if (Poly is { IsZero: false, DominatorSign: < 0 }) 
            Poly = Poly.Negate();
        if (other.Poly is { IsZero: false, DominatorSign: < 0 }) 
            other.Poly = other.Poly.Negate();
        return Poly.Equals(other.Poly);
    }

    public override int GetHashCode() {
        if (Poly is { IsZero: false, DominatorSign: < 0 })
            Poly = Poly.Negate();
        return Poly.GetHashCode();
    }

    public override int CompareToInternal(IntConstraint other) {
        if (Poly is { IsZero: false, DominatorSign: < 0 })
            Poly = Poly.Negate();
        if (((IntEq)other).Poly is { IsZero: false, DominatorSign: < 0 })
            ((IntEq)other).Poly = ((IntEq)other).Poly.Negate();
        return Poly.CompareTo(((IntEq)other).Poly);
    }

    public override string ToString() {
        var (pos, neg) = Poly.GetPosNeg();
        return $"{pos} = {neg}";
    }

    static int simplifyCnt;

    public SimplifyResult Simplify(NielsenNode node) {
        simplifyCnt++;
        if (Poly.TryGetConst(out BigInteger val))
            return val.IsZero ? SimplifyResult.Satisfied : SimplifyResult.Conflict;
        var bounds = Poly.GetBounds(node);
        if (!bounds.Contains(0))
            return SimplifyResult.Conflict;
        if (bounds.IsUnit)
            return SimplifyResult.Satisfied;
#if false
        // Normalization by division
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
        if (!offset.IsZero) {
            var r = BigInteger.Remainder(offset, gcd);
            if (!r.IsZero)
                return SimplifyResult.Conflict;
        }
        Poly = Poly.Div(gcd);
#endif
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

        var monomials = Poly.Monomials();

        foreach (var n in monomials) {
            if (n.Variables.Count == 0) {
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
            if (n.Coefficient.IsOne || n.Coefficient == BigInteger.MinusOne)
                continue;
            var lb = PDD<BigInteger>.GetBounds(node, monomials.Where((_, j) => i0 != j));
            if (lb.IsFull)
                continue;
            if (n.Coefficient.Sign >= 0)
                lb = lb.Negate();

            lb /= BigInteger.Abs(n.Coefficient);
            switch (node.AddLowerIntBound(r.Var, lb.Min)) {
                case SimplifyResult.Conflict:
                    reason = BacktrackReasons.Arithmetic;
                    return SimplifyResult.Conflict;
                case SimplifyResult.Restart:
                    restart = true;
                    break;
            }
            switch (node.AddHigherIntBound(r.Var, lb.Max)) {
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

#if false
    public bool GetLess(Dictionary<NamedStrToken, Dictionary<NamedStrToken, uint>> largerVars) {
        var (pos, neg) = Poly.GetPosNeg();
        bool swp = false;
        if (neg.Count == 1) {
            (pos, neg) = (neg, pos);
            swp = true;
        }
        if (pos.Count != 1 || !pos.First().t.IsLinearVariable(out var i) || i is not LenVar lv)
            return true;
        if (neg.ConstPart.IsZero)
            return true;
        var v = lv.Var;
        Debug.Assert(swp ? neg.ConstPart.IsNeg : neg.ConstPart.IsPos);
        if (!largerVars.TryGetValue(v, out var set))
            largerVars.Add(v, set = []);

        foreach (var p in neg.NonConst) {
            Debug.Assert(swp ? p.occ.IsNeg : p.occ.IsPos);
            if (!p.t.IsLinearVariable(out var i2) || i2 is not LenVar lv2)
                continue;
            if (!set.TryGetValue(lv2.Var, out uint val)) {
                set.Add(v, (uint)(BigInteger)p.occ);
            }
            else if (val < p.occ) {
                set[v] = (uint)(BigInteger)p.occ;
            }
            if (largerVars.TryGetValue(lv2.Var, out var set2) && set2.ContainsKey(v))
                // x < ... and y < ... + x + ...
                // Conflict
                return false;
        }
        return true;
    }
#endif

    public override BoolExpr ToExpr(NielsenGraph graph) => 
        graph.Ctx.MkEq(Poly.ToExpr(graph), graph.Ctx.MkInt(0));

    public override void CollectSymbols(NonTermSet nonTermSet, HashSet<CharToken> alphabet) =>
        Poly.CollectSymbols(nonTermSet, alphabet);

    public override IntConstraint Negate() =>
        new IntNonEq(Poly);
}