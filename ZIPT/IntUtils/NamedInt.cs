using System.Numerics;
using Microsoft.Z3;
using ZIPT.Constraints;
using ZIPT.Strings;
using ZIPT.Strings.Tokens;

namespace ZIPT.IntUtils;

public abstract class NamedInt : IComparable<NamedInt> {
    public abstract InfNum<BigInteger> MinLen { get; }
    public abstract int CompareToInternal(NamedInt other);
    public int CompareTo(NamedInt? other) {
        if (other is null)
            return 1;
        if (ReferenceEquals(other, this))
            return 0;
        int cmp = GetType().TypeHandle.Value.CompareTo(other.GetType().TypeHandle.Value);
        return cmp != 0 ? cmp : CompareToInternal(other);
    }
    public abstract void CollectSymbols(NonTermSet nonTermSet, HashSet<CharToken> alphabet);
    public abstract IntExpr ToExpr(NielsenGraph graph);
    public abstract override string ToString();
}