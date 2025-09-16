using Microsoft.Z3;
using System.Diagnostics;
using ZIPT.Constraints.Modifier;
using ZIPT.IntUtils;
using ZIPT.Strings.Chunks;
using ZIPT.Strings.Tokens;

namespace ZIPT.Constraints.ConstraintElement.AuxConstraints;

public sealed class StrNonEq : StrEqBase {

    public StrNonEq(Str lhs, Str rhs) : base(lhs, rhs) { }

    public override StrNonEq Apply(Subst subst, NielsenNode node) =>
        new(node.Env.StrManager.Subst(LHS, subst),
            node.Env.StrManager.Subst(RHS, subst));

    public override StrNonEq Apply(Interpretation itp) =>
        new(itp.Env.StrManager.Subst(LHS, itp),
            itp.Env.StrManager.Subst(RHS, itp));

    SimplifyResult Simplify(NielsenNode node, bool dir) {
        while (LHS.IsNonEmpty() && RHS.IsNonEmpty()) {
            Debug.Assert(LHS.IsNonEmpty());
            Debug.Assert(RHS.IsNonEmpty());

            if (SimplifySame(node.Env, dir))
                continue;

            if (LHS[dir] is CharToken c1 && RHS[dir] is CharToken c2 && !c1.Equals(c2))
                return SimplifyResult.Satisfied;

            if (SimplifyPower(node, dir))
                continue;
            break;
        }
        return SimplifyResult.Proceed;
    }

    protected override SimplifyResult SimplifyAndPropagateInternal(NielsenNode node, DetModifier sConstr, ref BacktrackReasons reason) {
        Log.WriteLine($"Simplify DisEq: {LHS} != {RHS}");
        SimplifyResult res;
        Debug.Assert(IsSorted());
        if ((res = Simplify(node, true)) != SimplifyResult.Proceed) {
            reason = res == SimplifyResult.Conflict ? BacktrackReasons.SymbolClash : reason;
            SortStr();
            return res;
        }
        if ((res = Simplify(node, false)) != SimplifyResult.Proceed) {
            reason = res == SimplifyResult.Conflict ? BacktrackReasons.SymbolClash : reason;
            SortStr();
            return res;
        }

        SortStr();

        if (LHS.IsEmpty() && RHS.IsEmpty())
            return SimplifyResult.Conflict;

        if (!LHS.IsEmpty() && !RHS.IsEmpty()) 
            return SimplifyResult.Proceed;

        var eq = LHS.IsEmpty() ? RHS : LHS;
        var l = LenVar.MkLenPoly(eq, node.Env);
        if (node.IsLt(node.Env.ZeroInt, l))
            return SimplifyResult.Satisfied;
        return SimplifyResult.Proceed;
    }

    public override ModifierBase Extend(NielsenNode node, Dictionary<NamedInt, PDD<BigRational>> intSubst) => 
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
        HashCode.Combine(LHS, RHS) * 737001851;

    public override string ToString() => $"{LHS} \u2260 {RHS}";
}