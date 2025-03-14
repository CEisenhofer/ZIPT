using System.Diagnostics;
using Microsoft.Z3;
using StringBreaker.Constraints;
using StringBreaker.Constraints.ConstraintElement;

namespace StringBreaker.Tokens;

public sealed class CharToken : StrToken {

    public char Value { get; }

    public CharToken(char value) =>
        Value = value;

    public override bool Ground => true;
    public override bool IsNullable(NielsenNode node) => false;

    public override Str Apply(Subst subst) => [this];
    public override Str Apply(Interpretation subst) => [this];

    public override List<(Str str, List<IntConstraint> sideConstraints, Subst? varDecomp)> GetPrefixes() =>
        // P(a) := {}
        [([], [], null)];

    public override Expr ToExpr(NielsenGraph graph) {
        Expr? e = graph.Propagator.GetCachedStrExpr(this);
        if (e is not null)
            return e;
        e = graph.Ctx.MkFreshConst(Value.ToString(), graph.Propagator.StringSort);
        e = graph.Ctx.MkUserPropagatorFuncDecl(e.FuncDecl.Name.ToString(), [], graph.Propagator.StringSort).Apply();
        graph.Propagator.SetCachedExpr(this, e);
        return e;
    }

    public override bool RecursiveIn(StrVarToken v) => false;

    protected override int CompareToInternal(StrToken other) {
        Debug.Assert(other is CharToken);
        return Value.CompareTo(((CharToken)other).Value);
    }

    public override bool Equals(StrToken? other) =>
        other is CharToken token && Equals(token);

    public bool Equals(CharToken other) =>
        Value == other.Value;

    public override int GetHashCode() => 21954391 * Value;

    public override string ToString(NielsenGraph? graph) => Value.ToString();
}