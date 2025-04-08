using Microsoft.Z3;
using StringBreaker.Constraints;
using StringBreaker.Strings.Tokens;

namespace StringBreaker.IntUtils;

public abstract class StrDepIntVar : NonTermInt {

    public StrVarToken Var { get; }
    public sealed override Len MinLen => 0;

    protected StrDepIntVar(StrVarToken v) =>
        Var = v;

    public override int CompareToInternal(NonTermInt other) =>
        Var.CompareTo(((StrDepIntVar)other).Var);

    public override void CollectSymbols(HashSet<NamedStrToken> vars, HashSet<SymCharToken> sChars, 
        HashSet<IntVar> iVars, HashSet<CharToken> alphabet) => vars.Add(Var);
}