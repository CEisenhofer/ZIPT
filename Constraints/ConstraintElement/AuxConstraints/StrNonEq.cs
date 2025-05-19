using System.Diagnostics;
using Microsoft.Z3;
using ZIPT.MiscUtils;
using ZIPT.Constraints.Modifier;
using ZIPT.IntUtils;
using ZIPT.Tokens;

namespace ZIPT.Constraints.ConstraintElement.AuxConstraints;

public sealed class StrNonEq : StrEqBase {

    public StrNonEq(Str lhs, Str rhs) : base(lhs, rhs) { }

    public override StrNonEq Clone() => new(LHS, RHS);

    SimplifyResult SimplifyDir(NielsenNode node, bool dir) {
        var s1 = LHS;
        var s2 = RHS;
        SortStr(ref s1, ref s2, dir);
        while (LHS.IsNonEmpty() && RHS.IsNonEmpty()) {
            SortStr(ref s1, ref s2, dir);
            Debug.Assert(s1.Count > 0);
            Debug.Assert(s2.Count > 0);

            if (SimplifySame(s1, s2, dir))
                continue;

            if (s1.Peek(dir) is UnitToken u1 && s2.Peek(dir) is UnitToken u2 && node.AreDiseq(u1, u2))
                return SimplifyResult.Satisfied;

            if (SimplifyPower(node, s1, s2, dir))
                continue;
            break;
        }
        return SimplifyResult.Proceed;
    }

    protected override SimplifyResult SimplifyAndPropagateInternal(NielsenNode node,
        DetModifier sConstr,
        ref BacktrackReasons reason) {
        Log.WriteLine($"Simplify DisEq: {LHS} != {RHS}");
        SimplifyResult res;
        if ((res = SimplifyDir(node, true)) != SimplifyResult.Proceed) {
            reason = res == SimplifyResult.Conflict ? BacktrackReasons.SymbolClash : reason;
            return res;
        }
        if ((res = SimplifyDir(node, false)) != SimplifyResult.Proceed) {
            reason = res == SimplifyResult.Conflict ? BacktrackReasons.SymbolClash : reason;
            return res;
        }

        if (LHS.IsEmpty() && RHS.IsEmpty())
            return SimplifyResult.Conflict;

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