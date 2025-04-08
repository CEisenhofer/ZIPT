using Microsoft.Z3;
using StringBreaker.Constraints.Modifier;
using StringBreaker.IntUtils;
using StringBreaker.Strings;
using StringBreaker.Strings.Tokens;

namespace StringBreaker.Constraints.ConstraintElement.AuxConstraints;

public sealed class StrNonEq : StrEqBase {

    public StrNonEq(NielsenContext ctx, StrRef lhs, StrRef rhs) : base(ctx, lhs, rhs) { }

    public override StrNonEq Clone(NielsenContext ctx) => new(ctx, LHS, RHS);

    SimplifyResult SimplifyDir(NielsenContext ctx, bool dir) {
        var s1 = LHS;
        var s2 = RHS;
        SortStr(ctx, ref s1, ref s2, dir);
        while (!LHS.IsEpsilon(ctx) && !RHS.IsEpsilon(ctx)) {

            SortStr(ctx, ref s1, ref s2, dir);
            if (SimplifySame(ctx, s1, s2, dir))
                continue;

            if (s1.Peek2(ctx, dir).Token is UnitToken u1 && s2.Peek2(ctx, dir).Token is UnitToken u2 && ctx.AreDiseq(u1, u2))
                return SimplifyResult.Satisfied;

            if (SimplifyPower(ctx, s1, s2, dir))
                continue;
            break;
        }
        return SimplifyResult.Proceed;
    }

    protected override SimplifyResult SimplifyInternal(NielsenContext ctx,
        List<Subst> newSubst, HashSet<Constraint> newSideConstr,
        ref BacktrackReasons reason) {
        Log.WriteLine($"Simplify DisEq: {LHS} != {RHS}");
        SimplifyResult res;
        if ((res = SimplifyDir(ctx, true)) != SimplifyResult.Proceed) {
            reason = res == SimplifyResult.Conflict ? BacktrackReasons.SymbolClash : reason;
            return res;
        }
        if ((res = SimplifyDir(ctx, false)) != SimplifyResult.Proceed) {
            reason = res == SimplifyResult.Conflict ? BacktrackReasons.SymbolClash : reason;
            return res;
        }

        bool e1 = LHS.IsEpsilon(ctx);
        bool e2 = RHS.IsEpsilon(ctx);

        if (e1 && e2)
            return SimplifyResult.Conflict;

        if (e1 || e2) {
            var eq = e1 ? RHS : LHS;
            var l = LenVar.MkLenPoly(eq);
            if (node.IsLt(new Poly(), l))
                return SimplifyResult.Satisfied;
            SortStr(ctx);
            return SimplifyResult.Proceed;
        }

        SortStr(ctx);
        return SimplifyResult.Proceed;
    }

    public override ModifierBase Extend(NielsenContext ctx) {
        throw new NotSupportedException();
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

    public override StrConstraint Negate(NielsenContext ctx) => new StrEq(ctx, LHS, RHS);

    public override BoolExpr ToExpr(NielsenContext ctx) =>
        ctx.Graph.Ctx.MkNot(ctx.Graph.Ctx.MkEq(LHS.ToExpr(ctx), RHS.ToExpr(ctx)));

    public override string ToString() => $"{LHS} \u2260 {RHS}";
}