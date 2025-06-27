using System.Diagnostics;
using Microsoft.Z3;
using ZIPT.Constraints;

namespace ZIPT.Tokens;

public sealed class SymCharToken : UnitToken {

    static int nextId;
    public int VarId { get; }

    public static void ResetCounter() => nextId = 0;

    public SymCharToken() => VarId = nextId++;

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
        return VarId.CompareTo(((SymCharToken)other).VarId);
    }

    public override bool Equals(StrToken? other) =>
        other is SymCharToken token && Equals(token);

    public bool Equals(SymCharToken other) =>
        VarId == other.VarId;

    public override int GetHashCode() => 855791621 * nextId;

    public override string ToString(NielsenGraph? graph) => "'" + VarId + "'";
}