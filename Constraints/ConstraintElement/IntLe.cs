using Microsoft.Z3;
using StringBreaker.IntUtils;
using StringBreaker.Tokens;

namespace StringBreaker.Constraints.ConstraintElement;

// Poly <= 0
public class IntLe : IntConstraint {

    public Poly Poly { get; set; }

    public IntLe(Poly poly) => Poly = poly;
    public IntLe(Poly lhs, Poly rhs) {
        lhs.SubPoly(rhs);
        Poly = lhs;
    }

    public override IntConstraint Clone() => 
        new IntLe(Poly.Clone());

    public override bool Equals(object? obj) => 
        obj is IntLe eq && Poly.Equals(eq.Poly);

    public bool Equals(IntLe other) =>
        Poly.Equals(other.Poly);

    public override int GetHashCode() =>
        Poly.GetHashCode();

    public override string ToString() {
        Poly.GetPosNeg(out var pos, out var neg);
        return $"{pos} \u2264 {neg}";
    }

    public override void Apply(Subst subst) => Poly = Poly.Apply(subst);
    public override void Apply(Interpretation subst) => Poly = Poly.Apply(subst);

    protected override SimplifyResult SimplifyInternal(NielsenNode node, List<Subst> substitution,
        HashSet<Constraint> newSideConstraints) {
        var bounds = Poly.GetBounds(node);
        if (bounds.Max.IsNeg)
            return SimplifyResult.Conflict;
        if (bounds.Min >= 0)
            return SimplifyResult.Satisfied;
        Poly = Poly.Simplify(node);
        if (Poly.IsConst(out Len val))
            return val <= 0 ? SimplifyResult.Satisfied : SimplifyResult.Conflict;
        int sig;
        if ((sig = Poly.IsUniLinear(out NonTermInt? v, out val)) != 0) {
            return sig == 1 
                ? node.AddHigherIntBound(v!, val) 
                : node.AddLowerIntBound(v!, val);
        }
        return SimplifyResult.Proceed;
        /*if (Poly.IsUniLinear(out IntVar? v, out val))
            return node.AddExactIntBound(v, val);
        return SimplifyResult.Proceed;
        var bounds = Poly.GetBounds(node);
        return !bounds.Contains(0) ? SimplifyResult.Conflict : SimplifyResult.Proceed;*/
    }

    public override BoolExpr ToExpr(NielsenGraph graph) =>
        graph.Ctx.MkLe(Poly.ToExpr(graph), graph.Ctx.MkInt(0));
    public override void CollectSymbols(HashSet<StrVarToken> vars, HashSet<CharToken> alphabet) {
        throw new NotImplementedException();
    }

    public override int CompareToInternal(IntConstraint other) =>
        Poly.CompareTo(((IntLe)other).Poly);
}