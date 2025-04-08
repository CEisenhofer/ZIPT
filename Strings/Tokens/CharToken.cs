using System.Diagnostics;
using Microsoft.Z3;
using StringBreaker.Constraints;

namespace StringBreaker.Strings.Tokens;

public sealed class CharToken : UnitToken {

    public char Value { get; }

    public CharToken(char value) =>
        Value = value;

    public override Str Apply(Subst subst) => [this];
    public override Str Apply(Interpretation itp) => [this];

    public override Expr ToExpr(int copyIdx, NielsenContext ctx) {
        Expr? e = ctx.Cache.GetCachedStrExpr(this, copyIdx);
        if (e is not null)
            return e;
        FuncDecl f = ctx.Graph.Ctx.MkFreshConstDecl(Value.ToString(), ctx.Cache.StringSort);
        e = ctx.Graph.Ctx.MkUserPropagatorFuncDecl(f.Name.ToString(), [], ctx.Cache.StringSort).Apply();
        ctx.Cache.SetCachedExpr(this, e, copyIdx);
        return e;
    }

    protected override int CompareToInternal(StrToken other) {
        Debug.Assert(other is CharToken);
        return Value.CompareTo(((CharToken)other).Value);
    }

    public override bool Equals(StrToken? other) =>
        other is CharToken token && Equals(token);

    public bool Equals(CharToken other) =>
        Value == other.Value;

    public override int GetHashCode() => 21954391 * Value;

    public override string ToString() => Value.ToString();
}