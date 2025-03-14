using Microsoft.Z3;
using StringBreaker.Tokens;

namespace StringBreaker.Constraints.ConstraintElement;

public abstract class IntConstraint : Constraint, IComparable<IntConstraint> {
    public abstract int CompareToInternal(IntConstraint other);
    public int CompareTo(IntConstraint? other) {
        if (other is null)
            return 1;
        if (ReferenceEquals(other, this))
            return 0;
        int cmp = GetType().TypeHandle.Value.CompareTo(other.GetType().TypeHandle.Value);
        return cmp != 0 ? cmp : CompareToInternal(other);
    }
}