using ZIPT.Constraints.Modifier;
using ZIPT.IntUtils;
using ZIPT.Tokens;

namespace ZIPT.Constraints.ConstraintElement;

public abstract class StrConstraint : Constraint, IComparable<StrConstraint> {
    public abstract bool Contains(NamedStrToken namedStrToken);
    public abstract ModifierBase Extend(NielsenNode node, Dictionary<NonTermInt, RatPoly> intSubst);
    public abstract int CompareToInternal(StrConstraint other);
    public int CompareTo(StrConstraint? other) {
        if (other is null)
            return 1;
        if (ReferenceEquals(other, this))
            return 0;
        int cmp = GetType().TypeHandle.Value.CompareTo(other.GetType().TypeHandle.Value);
        return cmp != 0 ? cmp : CompareToInternal(other);
    }
}