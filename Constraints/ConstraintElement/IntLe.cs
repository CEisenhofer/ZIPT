using Microsoft.Z3;
using StringBreaker.IntUtils;
using StringBreaker.Strings;
using StringBreaker.Strings.Tokens;

namespace StringBreaker.Constraints.ConstraintElement;

// Poly <= 0
public class IntLe : IntConstraint {

    public Poly Poly { get; set; }

    public IntLe(Poly poly) => Poly = poly;

    // rhs does not need to be cloned
    public IntLe(Poly lhs, Poly rhs) {
        lhs.Sub(rhs);
        Poly = lhs;
    }

    // rhs does not need to be cloned
    public static IntLe MkLt(Poly lhs, Poly rhs) {
        var ret = new IntLe(lhs.Clone(), rhs);
        ret.Poly.Plus(1);
        return ret;
    }

    // rhs does not need to be cloned
    public static IntLe MkLe(Poly lhs, Poly rhs) => new(lhs, rhs);

    public override Constraint Clone(NielsenContext ctx) => 
        new IntLe(Poly.Clone());

    public override bool Equals(object? obj) =>
        obj is IntLe le && Equals(le);

    public bool Equals(IntLe other) =>
        Poly.Equals(other.Poly);

    public override int GetHashCode() =>
        Poly.GetHashCode();

    public override string ToString() {
        Poly.GetPosNeg(out var pos, out var neg);
        return $"{pos} \u2264 {neg}";
    }

    public override void Apply(Subst subst) => Poly = Poly.Apply(subst);
    public override void Apply(Interpretation itp) => Poly = Poly.Apply(itp);

    protected override SimplifyResult SimplifyInternal(NielsenNode node, List<Subst> substitution,
        HashSet<Constraint> newSideConstraints, ref BacktrackReasons reason) {
        var bounds = Poly.GetBounds(node);
        if (!bounds.Max.IsPos)
            return SimplifyResult.Satisfied;
        if (bounds.Min.IsPos) {
            reason = BacktrackReasons.Arithmetic;
            return SimplifyResult.Conflict;
        }
        Poly = Poly.Simplify(node);
        if (Poly.IsConst(out Len val)) {
            if (val <= 0)
                return SimplifyResult.Satisfied;
            reason = BacktrackReasons.Arithmetic;
            return SimplifyResult.Conflict;
        }
        int sig;
        if ((sig = Poly.IsUniLinear(out NonTermInt? v, out val)) != 0) {
            var res = sig == 1 
                ? node.AddHigherIntBound(v!, -val) 
                : node.AddLowerIntBound(v!, val);
            if (res == SimplifyResult.Conflict)
                reason = BacktrackReasons.Arithmetic;
            return res == SimplifyResult.Restart ? SimplifyResult.RestartAndSatisfied : res;
        }
        return SimplifyResult.Proceed;
        /*if (Poly.IsUniLinear(out IntVar? v, out val))
            return node.AddExactIntBound(v, val);
        return SimplifyResult.Proceed;
        var bounds = Poly.GetBounds(node);
        return !bounds.Contains(0) ? SimplifyResult.Conflict : SimplifyResult.Proceed;*/
    }

    public override BoolExpr ToExpr(NielsenContext ctx) =>
        ctx.Graph.Ctx.MkLe(Poly.ToExpr(), ctx.Graph.Ctx.MkInt(0));
    
    public override void CollectSymbols(HashSet<NamedStrToken> vars, HashSet<SymCharToken> sChars, 
        HashSet<IntVar> iVars, HashSet<CharToken> alphabet) =>
        Poly.CollectSymbols(vars, sChars, iVars, alphabet);

    public override IntConstraint Negate() =>
        MkLt(new Poly(), Poly);

    public override int CompareToInternal(IntConstraint other) =>
        Poly.CompareTo(((IntLe)other).Poly);
}