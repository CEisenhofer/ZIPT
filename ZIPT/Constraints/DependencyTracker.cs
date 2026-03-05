using System.Diagnostics;

namespace ZIPT.Constraints;

// Tracks if some constraint depends on another constraint
// Tracks dependencies of derived constraints on original input constraints (bitvector).
// Used to report minimal unsat cores and to attach reasons to modifiers/constraints.
public class DependencyTracker {
    uint[] hasDependency; // a bitvector where the i-th bit indicates that constraint i from the input had an effect on the constraint

    public DependencyTracker(int cnt) => 
        hasDependency = new uint[cnt];

    public DependencyTracker(int cnt, int set) : this(cnt) {
        hasDependency[set / sizeof(uint)] = 1u << (set % sizeof(uint));
    }

    public static DependencyTracker? Merge(DependencyTracker? o1, DependencyTracker? o2) => 
        o1 is null ? o2 : o1.Merge(o2);

    public DependencyTracker Merge(DependencyTracker? other) {
        if (other is null || other.hasDependency.Length == 0)
            return this;
        if (hasDependency.Length == 0)
            return other;

        Debug.Assert(hasDependency.Length == other.hasDependency.Length);
        if (IsSuperSet(other))
            return this;
        if (other.IsSuperSet(this))
            return other;
        DependencyTracker result = new DependencyTracker(hasDependency.Length);
        for (int i = 0; i < hasDependency.Length; i++) {
            result.hasDependency[i] = hasDependency[i] | other.hasDependency[i];
        }
        return result;
    }

    bool IsSuperSet(DependencyTracker other) {
        for (int i = 0; i < other.hasDependency.Length; i++) {
            if ((hasDependency[i] & other.hasDependency[i]) != other.hasDependency[i])
                return false;
        }
        return true;
    }
}