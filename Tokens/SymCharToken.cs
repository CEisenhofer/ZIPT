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
        Expr? e = graph.Cache.GetCachedStrExpr(this, graph);
        if (e is not null)
            return e;
        FuncDecl f = graph.Ctx.MkFreshConstDecl("'" + nextId + "'", graph.Cache.StringSort);
        e = graph.Ctx.MkUserPropagatorFuncDecl(f.Name.ToString(), [], graph.Cache.StringSort).Apply();
        graph.Cache.SetCachedExpr(this, e, graph);
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