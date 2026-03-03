using Microsoft.Z3;
using System.Diagnostics;
using ZIPT.Constraints;
using ZIPT.MiscUtils;

namespace ZIPT.Strings.Tokens;

// Symbolic character token (a named unknown character). Used in character-range tracking and substitution.
public class SymCharToken : UnitToken { 

    public string Name { get; }

    public SymCharToken(NamedStrToken parent) {
        Name = "?" + parent.Name;
    }


    public SymCharToken(string name) {
        Log.Caller(nameof(Environment.GetOrCreateSymChar));
        Name = name;
    }

    public override bool Ground => true;
    public override bool RegexFree => true;
    public override bool Derivable => false;

    public override Expr ToExpr(Environment env, Dictionary<NamedStrToken, int> currentModificationCnt) {
        Expr? e = env.GetCachedStrExpr(this, currentModificationCnt);
        if (e is not null)
            return e;
        FuncDecl f = env.Ctx.MkFreshConstDecl(Name, env.StringSort);
        e = env.Ctx.MkUserPropagatorFuncDecl(f.Name.ToString(), [], env.StringSort).Apply();
        env.SetCachedExpr(this, e, currentModificationCnt);
        return e;
    }

    protected override int CompareToInternal(StrToken other) {
        Debug.Assert(other is SymCharToken);
        return string.Compare(Name, ((SymCharToken)other).Name, StringComparison.Ordinal);
    }

    public override void CollectSymbols(NonTermSet nonTermSet, CharacterSet alphabet) =>
        nonTermSet.Add(this);

    public override bool Equals(StrToken? other) => 
        other is SymCharToken token && Name == token.Name;

    public override int GetHashCode() =>
        185223239 * Name.GetHashCode();

    public override string ToString(NielsenGraph? graph) => Name;
}
