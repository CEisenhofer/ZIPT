using ZIPT.Constraints.Modifier;
using ZIPT.IntUtils;
using ZIPT.Strings.Tokens;

namespace ZIPT.Constraints.ConstraintElement;

public abstract class StrConstraint : Constraint, IComparable<StrConstraint> {

    public sealed override bool Shared => false;

    protected StrConstraint(DependencyTracker reason) : base(reason) { }

    public abstract bool Contains(NamedStrToken namedStrToken);

    // Produce a modifier that extends the search (splits, introduces a stabilizer, unwinds powers, etc.), or
    // return null when no extension is applicable at this time.
    public abstract ModifierBase? Extend(LocalInfo info, Dictionary<NamedInt, PDD<BigRational>> intSubst);
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