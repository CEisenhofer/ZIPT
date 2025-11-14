using System.Numerics;
using Microsoft.Z3;
using ZIPT.Constraints.Modifier;
using ZIPT.IntUtils;
using ZIPT.MiscUtils;
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
        Poly = lhs.Sub(rhs);
        if (!Poly.IsNormal)
            Poly = Poly.Negate();
    }

    public override IntNonEq Apply(Subst subst, NielsenNode node) {
        var (oldLen, newLen) = subst.GetLenReplacement(node.Env);
        var n = Poly.Substitute(oldLen, newLen);
        return ReferenceEquals(Poly, n) ? this : new IntNonEq(n);
    }

    public override Constraint Apply(CharSubst subst, NielsenNode node) => this;

    public override IntNonEq Apply(Interpretation itp) {
        var n = Poly;
        foreach (var kv in itp.IntVal) {
            n = n.Substitute(kv.Key, itp.Env.IntPDDManager.MkPDD(kv.Value));
        }
        return ReferenceEquals(Poly, n) ? this : new IntNonEq(n);
    }

    public override bool Equals(object? obj) =>
        obj is IntNonEq neq && Equals(neq);

    public bool Equals(IntNonEq other) {
        if (Poly is { IsZero: false, DominatorSign: < 0 })
            Poly = Poly.Negate();
        if (other.Poly is { IsZero: false, DominatorSign: < 0 })
            other.Poly = other.Poly.Negate();
        return Poly.Equals(other.Poly);
    }

    public override int CompareToInternal(IntConstraint other) {
        if (Poly is { IsZero: false, DominatorSign: < 0 })
            Poly = Poly.Negate();
        if (((IntNonEq)other).Poly is { IsZero: false, DominatorSign: < 0 })
            ((IntNonEq)other).Poly = ((IntNonEq)other).Poly.Negate();
        return Poly.CompareTo(((IntNonEq)other).Poly);
    }

    public override int GetHashCode() {
        if (Poly is { IsZero: false, DominatorSign: < 0 })
            Poly = Poly.Negate();
        return Poly.GetHashCode();
    }

    public override string ToString() {
        var (pos, neg) = Poly.GetPosNeg();
        return $"{pos} != {neg}";
    }

    protected override SimplifyResult SimplifyAndPropagateInternal(LocalInfo info, DetModifier sConstr, ref BacktrackReasons reason) {
        var bounds = Poly.GetBounds(info.CurrentNode);
        if (!bounds.Contains(0))
            return SimplifyResult.Satisfied;
        if (bounds.IsUnit) {
            reason = BacktrackReasons.Arithmetic;
            return SimplifyResult.Conflict;
        }
        if (Poly.TryGetConst(out BigInteger val)) {
            if (!val.IsZero)
                return SimplifyResult.Satisfied;
            reason = BacktrackReasons.Arithmetic;
            return SimplifyResult.Conflict;
        }
        return SimplifyResult.Proceed;
    }

    public override BoolExpr ToExpr(Environment env, Dictionary<NamedStrToken, int> currentModificationCnt) => 
        env.Ctx.MkNot(env.Ctx.MkEq(Poly.ToExpr(env, currentModificationCnt), env.Ctx.MkInt(0)));

    public override void CollectSymbols(NonTermSet nonTermSet, CharacterSet alphabet) => 
        Poly.CollectSymbols(nonTermSet, alphabet);

    public override IntConstraint Negate() =>
        new IntEq(Poly);
}