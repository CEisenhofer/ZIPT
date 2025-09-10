using System.Diagnostics;
using Microsoft.Z3;
using ZIPT.Constraints;
using ZIPT.Strings;

namespace ZIPT.Strings.Tokens;

public sealed class CharToken : UnitToken {

    public char Value { get; }

    public CharToken(char value) =>
        Value = value;

    public override Expr ToExpr(NielsenGraph graph) {
        Expr? e = graph.Env.GetCachedStrExpr(this, graph);
        if (e is not null)
            return e;
        FuncDecl f = graph.Ctx.MkFreshConstDecl(Value.ToString(), graph.Env.StringSort);
        e = graph.Ctx.MkUserPropagatorFuncDecl(f.Name.ToString(), [], graph.Env.StringSort).Apply();
        graph.Env.SetCachedExpr(this, e, graph);
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

    public override string ToString(NielsenGraph? graph) => Value.ToString();
}