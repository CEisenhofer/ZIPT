﻿using Microsoft.Z3;
using ZIPT.Constraints;
using ZIPT.Tokens;

namespace ZIPT.IntUtils;

public abstract class NonTermInt : IComparable<NonTermInt> {
    public abstract BigIntInf MinLen { get; }
    public abstract IntPoly Apply(Subst subst);
    public abstract IntPoly Apply(Interpretation subst);
    public abstract int CompareToInternal(NonTermInt other);
    public int CompareTo(NonTermInt? other) {
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