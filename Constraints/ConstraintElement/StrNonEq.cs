using System.Diagnostics;
using Microsoft.Z3;
using StringBreaker.Constraints.Modifier;
using StringBreaker.MiscUtils;
using StringBreaker.Tokens;

namespace StringBreaker.Constraints.ConstraintElement;

public sealed class StrNonEq : StrEqBase {

    public StrNonEq(Str lhs, Str rhs) : base(lhs, rhs) { }

    public override StrNonEq Clone() => new(LHS, RHS);

    protected override SimplifyResult SimplifyInternal(NielsenNode node, List<Subst> newSubst,
        HashSet<Constraint> newSideConstr) {
        while (LHS.NonEmpty() && RHS.NonEmpty()) {
            var lhs1 = LHS.First();
            var rhs1 = RHS.First();
            Debug.Assert(lhs1 is not null);
            Debug.Assert(rhs1 is not null);
            if (!lhs1.Equals(rhs1)) {
                if (lhs1 is CharToken && rhs1 is CharToken)
                    return SimplifyResult.Satisfied;
                return SimplifyResult.Proceed;
            }
            LHS.DropFirst();
            RHS.DropFirst();
        }
        while (LHS.NonEmpty() && RHS.NonEmpty()) {
            var lhs1 = LHS.Last();
            var rhs1 = RHS.Last();
            Debug.Assert(lhs1 is not null);
            Debug.Assert(rhs1 is not null);
            if (!lhs1.Equals(rhs1)) {
                if (lhs1 is CharToken && rhs1 is CharToken)
                    return SimplifyResult.Satisfied;
                return SimplifyResult.Proceed;
            }
            LHS.DropLast();
            RHS.DropLast();
        }
        if (LHS.IsEmpty() && RHS.IsEmpty())
            return SimplifyResult.Conflict;

        return SimplifyResult.Proceed;
    }

    public override ModifierBase Extend(NielsenNode node) {
        throw new NotImplementedException();
    }

    public override int CompareToInternal(StrConstraint other) {
        StrNonEq otherNonEq = (StrNonEq)other;
        int cmp = LHS.Count.CompareTo(otherNonEq.LHS.Count);
        if (cmp != 0)
            return cmp;
        cmp = RHS.Count.CompareTo(otherNonEq.RHS.Count);
        if (cmp != 0)
            return cmp;
        cmp = LHS.CompareTo(otherNonEq.LHS);
        return cmp != 0 ? cmp : RHS.CompareTo(otherNonEq.RHS);
    }

    public override StrConstraint Negate() => new StrEq(LHS, RHS);
    public override BoolExpr ToExpr(NielsenGraph graph) =>
        graph.Ctx.MkNot(graph.Ctx.MkEq(LHS.ToExpr(graph), RHS.ToExpr(graph)));

    public override int GetHashCode() =>
        208750709 + LHS.GetHashCode() + 125681929 * RHS.GetHashCode();

    public override string ToString() => $"{LHS} \u2260 {RHS}";
}