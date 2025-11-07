using System.Diagnostics;
using System.Runtime.InteropServices;
using Microsoft.Z3;
using ZIPT.Constraints;
using ZIPT.MiscUtils;
using ZIPT.Strings.Chunks;

namespace ZIPT.Strings.Tokens;

public sealed class CharToken : UnitToken {

    public char Value { get; }

    public CharToken(char value) =>
        Value = value;

    public CharToken(uint value) =>
        Value = (char)value;

    public override bool Ground => true;
    public override bool RegexFree => true;
    public override bool Derivable => true;

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

    public override void CollectSymbols(NonTermSet nonTermSet, HashSet<CharToken> alphabet) =>
        alphabet.Add(this);

    public override MinTerms FirstMinTerms() => new(this);

    public override MinTerms LastMinTerms() => new(this);

    public override bool Equals(StrToken? other) =>
        other is CharToken token && Equals(token);

    public bool Equals(CharToken other) =>
        Value == other.Value;

    public override int GetHashCode() => 21954391 * Value;

    public override string ToString(NielsenGraph? graph) => Value.ToString();

    public override Str Derivative(Environment env, CharacterSet set, bool fwd) => 
        set.Contains(this) ? env.EmptyStr : env.FailStr;
}