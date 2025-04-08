using System.Diagnostics;
using Microsoft.Z3;
using StringBreaker.Constraints;

namespace StringBreaker.Strings.Tokens;

public sealed class SymCharToken : UnitToken {

    static int nextId;
    public int Id { get; }

    public static void ResetCounter() => nextId = 0;

    public SymCharToken() => Id = nextId++;

    public override Str Apply(Subst subst) => subst.ResolveVar(this);
    public override Str Apply(Interpretation itp) => [itp.ResolveVar(this)];

    public override Expr ToExpr(int copyIdx, NielsenContext ctx) {
        Expr? e = ctx.Cache.GetCachedStrExpr(this, copyIdx);
        if (e is not null)
            return e;
        FuncDecl f = ctx.Graph.Ctx.MkFreshConstDecl("'" + nextId + "'", ctx.Cache.StringSort);
        e = ctx.Graph.Ctx.MkUserPropagatorFuncDecl(f.Name.ToString(), [], ctx.Cache.StringSort).Apply();
        ctx.Cache.SetCachedExpr(this, e, copyIdx);
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

    public override string ToString() => "'" + Id + "'";
}