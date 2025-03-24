using System.Diagnostics;
using Microsoft.Z3;
using StringBreaker.IntUtils;
using StringBreaker.Tokens;

namespace StringBreaker.Constraints.ConstraintElement;

// Poly = 0
public class IntEq : IntConstraint {

    public Poly Poly { get; set; }

    public IntEq(Poly poly) => Poly = poly;

    public IntEq(Poly lhs, Poly rhs) {
        Poly = lhs.Clone();
        Poly.Sub(rhs);
    }

    public override IntConstraint Clone() => 
        new IntEq(Poly.Clone());

    public override bool Equals(object? obj) => 
        obj is IntEq eq && Equals(eq);

    public bool Equals(IntEq other) => 
        Poly.Equals(other.Poly);

    public override int GetHashCode() =>
        Poly.GetHashCode();

    public override string ToString() {
        Poly.GetPosNeg(out var pos, out var neg);
        return $"{pos} = {neg}";
    }

    public override void Apply(Subst subst) => 
        Poly = Poly.Apply(subst);

    public override void Apply(Interpretation itp) => 
        Poly = Poly.Apply(itp);

    protected override SimplifyResult SimplifyInternal(NielsenNode node, List<Subst> substitution,
        HashSet<Constraint> newSideConstraints, ref BacktrackReasons reason) {
        var bounds = Poly.GetBounds(node);
        if (!bounds.Contains(0)) {
            reason = BacktrackReasons.Arithmetic;
            return SimplifyResult.Conflict;
        }
        if (bounds.IsUnit)
            return SimplifyResult.Satisfied;
        Poly = Poly.Simplify(node);
        if (Poly.IsConst(out Len val)) {
            if (val == 0)
                return SimplifyResult.Satisfied;
            reason = BacktrackReasons.Arithmetic;
            return SimplifyResult.Conflict;
        }
        int sig;
        if ((sig = Poly.IsUniLinear(out NonTermInt? v, out val)) != 0) {
            var res = node.AddExactIntBound(v!, sig == 1 ? -val : val);
            if (res == SimplifyResult.Conflict)
                reason = BacktrackReasons.Arithmetic;
            return res == SimplifyResult.Restart ? SimplifyResult.RestartAndSatisfied : res;
        }
        return SimplifyResult.Proceed;
        /*var bounds = Poly.GetBounds(node);
        return !bounds.Contains(0) ? SimplifyResult.Conflict : SimplifyResult.Proceed;*/
    }

    public override BoolExpr ToExpr(NielsenGraph graph) => 
        graph.Ctx.MkEq(Poly.ToExpr(graph), graph.Ctx.MkInt(0));

    public override void CollectSymbols(HashSet<NamedStrToken> vars, HashSet<SymCharToken> sChars, 
        HashSet<IntVar> iVars, HashSet<CharToken> alphabet) =>
        Poly.CollectSymbols(vars, sChars, iVars, alphabet);

    public override IntConstraint Negate() =>
        new IntNonEq(Poly.Clone());

    public override int CompareToInternal(IntConstraint other) => 
        Poly.CompareTo(((IntEq)other).Poly);
}