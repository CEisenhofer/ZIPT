using Microsoft.Z3;
using StringBreaker.Constraints.Modifier;
using StringBreaker.IntUtils;
using StringBreaker.Tokens;

namespace StringBreaker.Constraints.ConstraintElement;

// Poly != 0
public class IntNonEq : IntConstraint {

    public IntPoly Poly { get; set; }

    public IntNonEq(IntPoly poly) => Poly = poly;

    public IntNonEq(IntPoly lhs, IntPoly rhs) {
        Poly = lhs.Clone();
        Poly.Sub(rhs);
    }

    public override IntConstraint Clone() => 
        new IntNonEq(Poly.Clone());

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
        Poly.GetPosNeg(out var pos, out var neg);
        return $"{pos} != {neg}";
    }

    public override void Apply(Subst subst) => 
        Poly = Poly.Apply(subst);

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
        if (Poly.IsConst(out BigInt val)) {
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
        new IntEq(Poly.Clone());
}