using System.Collections;
using System.Diagnostics;
using StringBreaker.Constraints.ConstraintElement;
using StringBreaker.Tokens;

namespace StringBreaker.Constraints;

public interface IIntConstraintSet : IConstraintSet {
    IntConstraint GetConstraint(int idx);
    IEnumerable<IntConstraint> EnumerateConstraints();
}

public class IntConstraintSet<T> : IEnumerable<T>, IIntConstraintSet where T : IntConstraint {

    readonly List<T> constraints;

    public IntConstraintSet(List<T> constraints) {
        constraints.Sort();
        this.constraints = constraints;
    }

    public bool Satisfied => constraints.All(equation => equation.Satisfied);
    public bool Violated => constraints.Any(equation => equation.Violated);
    public T this[int idx] => constraints[idx];
    public int Count => constraints.Count;

    public IntConstraint GetConstraint(int idx) => constraints[idx];

    public IEnumerable<IntConstraint> EnumerateConstraints() => constraints;
    public IEnumerable<Constraint> EnumerateBaseConstraints() => constraints;
    public bool Contains(T cnstr) => constraints.BinarySearch(cnstr) >= 0;
    public void Apply(Subst subst) {
        for (int i = 0; i < Count; i++) {
            constraints[i].Apply(subst);
        }
    }

    public IEnumerator<T> GetEnumerator() =>
        ((IEnumerable<T>)constraints).GetEnumerator();

    IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();

    public bool Remove(Constraint constraint) => 
        constraint is T t && constraints.Remove(t);

    public void RemoveAt(int idx) => constraints.RemoveAt(idx);

    public override bool Equals(object? obj) =>
        obj is IntConstraintSet<T> other && Equals(other);

    public bool Equals(IntConstraintSet<T> other) =>
        constraints.Count == other.constraints.Count && constraints.SequenceEqual(other.constraints);

    public override int GetHashCode() =>
        constraints.Aggregate(906270727, (current, cnstr) => current * 135719593 + cnstr.GetHashCode());

    public IntConstraintSet<T> Clone() {
        var newConstraints = new List<T> {
            Capacity = constraints.Count,
        };
        foreach (var v in constraints) {
            // Check again if it is not contained already - the constraints might have changed!
            int idx = newConstraints.BinarySearch(v);
            if (idx < 0)
                newConstraints.Insert(~idx, (T)v.Clone());
        }
        return new IntConstraintSet<T>(newConstraints);
    }

    public void Add(T t) {
        int idx = constraints.BinarySearch(t);
        if (idx < 0)
            constraints.Insert(~idx, t);
    }

    public override string ToString() =>
        Satisfied
            ? "\u22a4"
            : Violated
                ? "\u22a5"
                : string.Join(", ", constraints.Select(o => o.ToString()));

}