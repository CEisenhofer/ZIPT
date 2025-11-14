using Microsoft.Z3;
using System.Diagnostics;
using ZIPT.Constraints;

namespace ZIPT.Strings.Tokens;

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

    public override Expr ToExpr(Environment env, Dictionary<NamedStrToken, int> currentModificationCnt) => 
        env.Ctx.MkConst(Name, env.Ctx.CharSort);

    protected override int CompareToInternal(StrToken other) {
        Debug.Assert(other is SymCharToken);
        return string.Compare(Name, ((SymCharToken)other).Name, StringComparison.Ordinal);
    }

    public override void CollectSymbols(NonTermSet nonTermSet, HashSet<CharToken> alphabet) =>
        nonTermSet.Add(this);

    public override bool Equals(StrToken? other) => 
        other is SymCharToken token && Name == token.Name;

    public override int GetHashCode() =>
        185223239 * Name.GetHashCode();

    public override string ToString(NielsenGraph? graph) => Name;
}