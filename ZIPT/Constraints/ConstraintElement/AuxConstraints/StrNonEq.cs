using System.Diagnostics;
using Microsoft.Z3;
using ZIPT.MiscUtils;
using ZIPT.Constraints.Modifier;
using ZIPT.IntUtils;
using ZIPT.Tokens;

namespace ZIPT.Constraints.ConstraintElement.AuxConstraints;

public sealed class StrNonEq : StrEqBase {

    public StrNonEq(IStr lhs, IStr rhs) : base(lhs, rhs) { }

    public override StrNonEq Clone() => new(LHS, RHS);

    SimplifyResult SimplifyDir(NielsenNode node, ref uint i1, ref uint i2, bool dir) {
        var s1 = LHS;
        var s2 = RHS;
		SortStr(ref s1, ref i1, ref s2, ref i2, dir);
        while (LHS.IsNonEmpty() && RHS.IsNonEmpty()) {
            SortStr(ref s1, ref i1, ref s2, ref i2, dir);
            Debug.Assert(s1.IsNonEmpty());
            Debug.Assert(s2.IsNonEmpty());

            if (SimplifySame(s1, ref i1, s2, ref i2, dir))
                continue;

            if (s1.Peek(dir) is UnitToken u1 && s2.Peek(dir) is UnitToken u2 && node.AreDiseq(u1, u2))
                return SimplifyResult.Satisfied;

            if (SimplifyPower(node, s1, ref i1, s2, ref i2, dir))
                continue;
            break;
        }
        return SimplifyResult.Proceed;
    }

    protected override SimplifyResult SimplifyAndPropagateInternal(NielsenNode node, DetModifier sConstr, ref BacktrackReasons reason) {
        Log.WriteLine($"Simplify DisEq: {LHS} != {RHS}");
        SimplifyResult res;
        uint i1t = 0, i2t = 0;
        uint i1f = 0, i2f = 0;
        if ((res = SimplifyDir(node, ref i1t, ref i2t, true)) != SimplifyResult.Proceed) {
            reason = res == SimplifyResult.Conflict ? BacktrackReasons.SymbolClash : reason;
            return res;
        }
        if ((res = SimplifyDir(node, ref i1t, ref i2t, false)) != SimplifyResult.Proceed) {
            reason = res == SimplifyResult.Conflict ? BacktrackReasons.SymbolClash : reason;
            return res;
        }

        if (LHS.IsEmpty() && RHS.IsEmpty())
            return SimplifyResult.Conflict;

        LHS = LHS.Drop(i1t, i1f);
        RHS = RHS.Drop(i2t, i2f);

        if (LHS.IsEmpty() || RHS.IsEmpty()) {
            var eq = LHS.IsEmpty() ? RHS : LHS;
            var l = LenVar.MkLenPoly(eq);
            if (node.IsLt(new IntPoly(), l))
                return SimplifyResult.Satisfied;
            SortStr();
            return SimplifyResult.Proceed;
        }

        SortStr();
        return SimplifyResult.Proceed;
    }

    public override ModifierBase Extend(NielsenNode node, Dictionary<NonTermInt, RatPoly> intSubst) => 
        throw new NotSupportedException();

    public override int CompareToInternal(StrConstraint other) {
        StrNonEq otherNonEq = (StrNonEq)other;
        int cmp = LHS.Length.CompareTo(otherNonEq.LHS.Length);
        if (cmp != 0)
            return cmp;
        cmp = RHS.Length.CompareTo(otherNonEq.RHS.Length);
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