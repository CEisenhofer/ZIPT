using ZIPT.Constraints;
using ZIPT.Tokens;

namespace ZIPT.IntUtils;

// TODO: Do we still need this?
public abstract class StrDepIntVar : NonTermInt {

    public NamedStrToken Var { get; }
    public sealed override BigIntInf MinLen => 0;

    protected StrDepIntVar(NamedStrToken v) =>
        Var = v;

    public override int CompareToInternal(NonTermInt other) =>
        Var.CompareTo(((StrDepIntVar)other).Var);

    public override void CollectSymbols(NonTermSet nonTermSet, HashSet<CharToken> alphabet) => nonTermSet.Add(Var);
}