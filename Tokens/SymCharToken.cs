using System.Diagnostics;
using Microsoft.Z3;
using StringBreaker.Constraints;

namespace StringBreaker.Tokens;

public sealed class SymCharToken : UnitToken {

    static int nextId;
    public int Id { get; }

    public SymCharToken() => Id = nextId++;

    public override Str Apply(Subst subst) => subst.ResolveVar(this);
    public override Str Apply(Interpretation itp) => [itp.ResolveVar(this)];

    public override Expr ToExpr(NielsenGraph graph) {
        Expr? e = graph.Propagator.GetCachedStrExpr(this);
        if (e is not null)
            return e;
        e = graph.Ctx.MkFreshConst("'" + nextId + "'", graph.Propagator.StringSort);
        e = graph.Ctx.MkUserPropagatorFuncDecl(e.FuncDecl.Name.ToString(), [], graph.Propagator.StringSort).Apply();
        graph.Propagator.SetCachedExpr(this, e);
        return e;
    }

    protected override int CompareToInternal(StrToken other) {
        Debug.Assert(other is SymCharToken);
        return Id.CompareTo(((SymCharToken)other).Id);
    }

    public override bool Equals(StrToken? other) =>
        other is SymCharToken token && Equals(token);

    public bool Equals(SymCharToken other) =>
        Id == other.Id;

    public override int GetHashCode() => 855791621 * nextId;

    public override string ToString(NielsenGraph? graph) => "'" + Id + "'";
}