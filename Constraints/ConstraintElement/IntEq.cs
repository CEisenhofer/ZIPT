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
        Poly.SubPoly(rhs);
    }

    public override IntConstraint Clone() => 
        new IntEq(Poly.Clone());

    public override bool Equals(object? obj) => 
        obj is IntEq eq && Poly.Equals(eq.Poly);

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

    public override void Apply(Interpretation subst) => 
        Poly = Poly.Apply(subst);

    protected override SimplifyResult SimplifyInternal(NielsenNode node, List<Subst> substitution,
        HashSet<Constraint> newSideConstraints) {
        if (Poly.IsConst(out Len val))
            return val == 0 ? SimplifyResult.Satisfied : SimplifyResult.Conflict;
        if (Poly.IsUniLinear(out NonTermInt? v, out val))
            return node.AddExactIntBound(v, val);
        return SimplifyResult.Proceed;
        /*var bounds = Poly.GetBounds(node);
        return !bounds.Contains(0) ? SimplifyResult.Conflict : SimplifyResult.Proceed;*/
    }

    public override BoolExpr ToExpr(NielsenGraph graph) => 
        graph.Ctx.MkEq(Poly.ToExpr(graph), graph.Ctx.MkInt(0));

    public override void CollectSymbols(HashSet<StrVarToken> vars, HashSet<CharToken> alphabet) {
        throw new NotImplementedException();
    }

    public override int CompareToInternal(IntConstraint other) => 
        Poly.CompareTo(((IntEq)other).Poly);
}