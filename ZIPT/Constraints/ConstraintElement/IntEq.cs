using System.Diagnostics;
using System.Numerics;
using Microsoft.Z3;
using ZIPT.Constraints.Modifier;
using ZIPT.IntUtils;
using ZIPT.Strings.Tokens;

namespace ZIPT.Constraints.ConstraintElement;

// Poly = 0
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

    public override IntEq Clone() => new(this);

    public override bool Equals(object? obj) => 
        obj is IntEq eq && Equals(eq);

    public bool Equals(IntEq other) {
        // Poly == other.Poly || Poly == -other.Poly (this is the same => Normalize)
        if (!Poly.IsZero && Poly.First().occ.IsNeg) 
            Poly = Poly.Negate();
        if (!other.Poly.IsZero && other.Poly.First().occ.IsNeg) 
            other.Poly = other.Poly.Negate();
        return Poly.Equals(other.Poly);
    }

    public override int GetHashCode() {
        if (!Poly.IsZero && Poly.First().occ.IsNeg)
            Poly = Poly.Negate();
        return Poly.GetHashCode();
    }

    public override int CompareToInternal(IntConstraint other) {
        if (!Poly.IsZero && Poly.First().occ.IsNeg)
            Poly = Poly.Negate();
        if (!((IntEq)other).Poly.IsZero && ((IntEq)other).Poly.First().occ.IsNeg)
            ((IntEq)other).Poly = ((IntEq)other).Poly.Negate();
        return Poly.CompareTo(((IntEq)other).Poly);
    }

    public override string ToString() {
        var (pos, neg) = Poly.GetPosNeg();
        return $"{pos} = {neg}";
    }

    public override void Apply(Interpretation itp) => 
        Poly = Poly.Apply(itp);

    static int simplifyCnt;

    public SimplifyResult Simplify(NielsenNode node) {
        simplifyCnt++;
        Poly = Poly.Simplify(node);
        if (Poly.IsConst(out BigInteger val))
            return val.IsZero ? SimplifyResult.Satisfied : SimplifyResult.Conflict;
        var bounds = Poly.GetBounds(node);
        if (!bounds.Contains(0))
            return SimplifyResult.Conflict;
        if (bounds.IsUnit)
            return SimplifyResult.Satisfied;
        // Normalization by division
        BigInteger c = Poly.ConstPart;
        BigInteger gcd = Poly.NonConst.First().occ.Abs();
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
        if (!c.IsZero) {
            var r = BigInteger.Remainder(c, gcd);
            if (!r.IsZero)
                return SimplifyResult.Conflict;
        }
        Poly = Poly.Div(gcd);
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
            int i0 = i++;
            var lb = PDD<BigInteger>.GetBounds(node, Poly.Where((_, j) => i0 != j));
            if (lb.IsFull)
                continue;
            if (!n.occ.IsNeg)
                lb = lb.Negate();

            lb /= n.occ.Abs();
            switch (node.AddLowerIntBound(r.t, lb.Min)) {
                case SimplifyResult.Conflict:
                    reason = BacktrackReasons.Arithmetic;
                    return SimplifyResult.Conflict;
                case SimplifyResult.Restart:
                    restart = true;
                    break;
            }
            switch (node.AddHigherIntBound(r.t, lb.Max)) {
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

    public override BoolExpr ToExpr(NielsenGraph graph) => 
        graph.Ctx.MkEq(Poly.ToExpr(graph), graph.Ctx.MkInt(0));

    public override void CollectSymbols(NonTermSet nonTermSet, HashSet<CharToken> alphabet) =>
        Poly.CollectSymbols(nonTermSet, alphabet);

    public override IntConstraint Negate() =>
        new IntNonEq(Poly);
}