using Microsoft.Z3;
using System.Diagnostics;
using ZIPT.Constraints.Modifier;
using ZIPT.IntUtils;
using ZIPT.Strings.Chunks;
using ZIPT.Strings.Tokens;

namespace ZIPT.Constraints.ConstraintElement.AuxConstraints;

public sealed class StrNonEq : StrEqBase {

    public StrNonEq(Str lhs, Str rhs) : base(lhs, rhs) {
        Debug.Assert(lhs.RegexFree);
        Debug.Assert(rhs.RegexFree);
    }

    public override StrNonEq Apply(Subst subst, NielsenNode node) {
        var lhs = node.Env.StrManager.Subst(LHS, subst);
        var rhs = node.Env.StrManager.Subst(RHS, subst);
        SortStr(ref lhs, ref rhs, true);
        if (ReferenceEquals(lhs, LHS) && ReferenceEquals(rhs, RHS))
            return this;
        return new StrNonEq(lhs, rhs);
    }

    public override StrNonEq Apply(CharSubst subst, NielsenNode node) {
        var lhs = node.Env.StrManager.Subst(node.Env, LHS, subst);
        var rhs = node.Env.StrManager.Subst(node.Env, RHS, subst);
        SortStr(ref lhs, ref rhs, true);
        if (ReferenceEquals(lhs, LHS) && ReferenceEquals(rhs, RHS))
            return this;
        return new StrNonEq(lhs, rhs);
    }
    
    public override StrNonEq Apply(Interpretation itp) {
        var lhs = itp.Env.StrManager.Subst(LHS, itp);
        var rhs = itp.Env.StrManager.Subst(RHS, itp);
        SortStr(ref lhs, ref rhs, true);
        if (ReferenceEquals(lhs, LHS) && ReferenceEquals(rhs, RHS))
            return this;
        return new StrNonEq(lhs, rhs);
    }

    SimplifyResult Simplify(LocalInfo info, bool fwd) {
        while (LHS.IsNonEmpty() && RHS.IsNonEmpty()) {
            Debug.Assert(LHS.IsNonEmpty());
            Debug.Assert(RHS.IsNonEmpty());

            if (SimplifySame(info.Env, fwd))
                continue;

            if (LHS[fwd] is CharToken c1 && RHS[fwd] is CharToken c2 && !c1.Equals(c2))
                return SimplifyResult.Satisfied;

            if (SimplifyPower(info, fwd))
                continue;
            break;
        }
        return SimplifyResult.Proceed;
    }

    protected override SimplifyResult SimplifyAndPropagateInternal(LocalInfo info, DetModifier sConstr, ref BacktrackReasons reason) {
        Log.WriteLine($"Simplify DisEq: {LHS} != {RHS}");
        SimplifyResult res;
        Debug.Assert(IsSorted());
        if ((res = Simplify(info, true)) != SimplifyResult.Proceed) {
            reason = res == SimplifyResult.Conflict ? BacktrackReasons.SymbolClash : reason;
            SortStr();
            return res;
        }
        if ((res = Simplify(info, false)) != SimplifyResult.Proceed) {
            reason = res == SimplifyResult.Conflict ? BacktrackReasons.SymbolClash : reason;
            SortStr();
            return res;
        }

        SortStr();

        if (LHS.IsEmpty() && RHS.IsEmpty())
            return SimplifyResult.Conflict;

        if (!LHS.IsEmpty() && !RHS.IsEmpty()) 
            return SimplifyResult.Proceed;

        return SimplifyResult.Proceed;
    }

    public override ModifierBase? Extend(NielsenNode node, Dictionary<NamedInt, PDD<BigRational>> intSubst) => 
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

    public override BoolExpr ToExpr(Environment env, Dictionary<NamedStrToken, int> currentModificationCnt) =>
        env.Ctx.MkNot(env.Ctx.MkEq(LHS.ToExpr(env, currentModificationCnt), RHS.ToExpr(env, currentModificationCnt)));

    public override int GetHashCode() =>
        HashCode.Combine(LHS, RHS) * 737001851;

    public override string ToString() => $"{LHS} \u2260 {RHS}";
}