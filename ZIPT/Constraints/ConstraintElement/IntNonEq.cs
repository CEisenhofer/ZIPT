using System.Numerics;
using Microsoft.Z3;
using ZIPT.Constraints.Modifier;
using ZIPT.IntUtils;
using ZIPT.Strings.Tokens;

namespace ZIPT.Constraints.ConstraintElement;

// Poly != 0
public class IntNonEq : IntConstraint {

    public PDD<BigInteger> Poly { get; set; }

    public IntNonEq(IntNonEq eq) {
        Poly = eq.Poly;
    }

    public IntNonEq(PDD<BigInteger> poly) {
        Poly = poly;
        if (!Poly.IsNormal)
            Poly = Poly.Negate();
    }

    public IntNonEq(PDD<BigInteger> lhs, PDD<BigInteger> rhs) {
        Poly = lhs;
        Poly = Poly.Sub(rhs);
        if (!Poly.IsNormal)
            Poly = Poly.Negate();
    }

    public override Constraint Clone() => 
        new IntNonEq(this);

    public override bool Equals(object? obj) =>
        obj is IntNonEq neq && Equals(neq);

    public bool Equals(IntNonEq other) {
        if (!Poly.IsZero && Poly.First().occ.IsNeg)
            Poly = Poly.Negate();
        if (!other.Poly.IsZero && other.Poly.First().occ.IsNeg)
            other.Poly = other.Poly.Negate();
        return Poly.Equals(other.Poly);
    }

    public override int CompareToInternal(IntConstraint other) {
        if (!Poly.IsZero && Poly.First().occ.IsNeg)
            Poly = Poly.Negate();
        if (!((IntNonEq)other).Poly.IsZero && ((IntNonEq)other).Poly.First().occ.IsNeg)
            ((IntNonEq)other).Poly = ((IntNonEq)other).Poly.Negate();
        return Poly.CompareTo(((IntNonEq)other).Poly);
    }

    public override int GetHashCode() {
        if (!Poly.IsZero && Poly.First().occ.IsNeg)
            Poly = Poly.Negate();
        return Poly.GetHashCode();
    }

    public override string ToString() {
        var (pos, neg) = Poly.GetPosNeg();
        return $"{pos} != {neg}";
    }

    public override void Apply(Interpretation itp) => 
        Poly = Poly.Apply(itp);

    protected override SimplifyResult SimplifyAndPropagateInternal(NielsenNode node, DetModifier sConstr, ref BacktrackReasons reason) {
        var bounds = Poly.GetBounds(node);
        if (!bounds.Contains(0))
            return SimplifyResult.Satisfied;
        if (bounds.IsUnit) {
            reason = BacktrackReasons.Arithmetic;
            return SimplifyResult.Conflict;
        }
        Poly = Poly.Simplify(node);
        if (Poly.IsConst(out BigInteger val)) {
            if (!val.IsZero)
                return SimplifyResult.Satisfied;
            reason = BacktrackReasons.Arithmetic;
            return SimplifyResult.Conflict;
        }
        return SimplifyResult.Proceed;
    }

    public override BoolExpr ToExpr(NielsenGraph graph) => 
        graph.Ctx.MkNot(graph.Ctx.MkEq(Poly.ToExpr(graph), graph.Ctx.MkInt(0)));

    public override void CollectSymbols(NonTermSet nonTermSet, HashSet<CharToken> alphabet) => 
        Poly.CollectSymbols(nonTermSet, alphabet);

    public override IntConstraint Negate() =>
        new IntEq(Poly);
}