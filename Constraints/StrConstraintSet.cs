using System.Collections;
using System.Diagnostics;
using StringBreaker.Constraints.ConstraintElement;
using StringBreaker.MiscUtils;
using StringBreaker.Strings;
using StringBreaker.Strings.Tokens;

namespace StringBreaker.Constraints;

public interface IStrConstraintSet : IConstraintSet {
    bool Contains(StrVarToken v);
    StrConstraint GetConstraint(int idx);
    IEnumerable<StrConstraint> EnumerateConstraints();
}

public class StrConstraintSet<T> : IEnumerable<T>, IStrConstraintSet where T : StrConstraint {

    readonly List<T> constraints;

    public StrConstraintSet(List<T> constraints) {
        constraints.Sort();
        this.constraints = constraints;
    }

    public bool Satisfied => constraints.All(equation => equation.Satisfied);
    public bool Violated => constraints.Any(equation => equation.Violated);
    public T this[int idx] => constraints[idx];
    public int Count => constraints.Count;

    public StrConstraint GetConstraint(int idx) => constraints[idx];

    public IEnumerable<StrConstraint> EnumerateConstraints() => constraints;
    public IEnumerable<Constraint> EnumerateBaseConstraints() => constraints;

    public IEnumerator<T> GetEnumerator() =>
        ((IEnumerable<T>)constraints).GetEnumerator();

    IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();

    public bool Contains(StrVarToken v) =>
        constraints.Any(eq => eq.Contains(v));

    public bool Remove(Constraint constraint) =>
        constraint is T t && constraints.Remove(t);

    public void RemoveAt(int idx) => constraints.RemoveAt(idx);

    public override bool Equals(object? obj) =>
        obj is StrConstraintSet<T> other && Equals(other);

    public bool Equals(StrConstraintSet<T> other) =>
        constraints.Count == other.constraints.Count && constraints.SequenceEqual(other.constraints);

    public override int GetHashCode() =>
        constraints.Aggregate(906270727, (current, cnstr) => current * 135719593 + cnstr.GetHashCode());

    public StrConstraintSet<T> Clone() {
        var newConstraints = new List<T> {
            Capacity = constraints.Count,
        };
        foreach (var v in constraints) {
            // Check again if it is not contained already - the constraints might have changed!
            int idx = newConstraints.BinarySearch(v);
            if (idx < 0)
                newConstraints.Insert(~idx, (T)v.Clone());
        }
        return new StrConstraintSet<T>(newConstraints);
    }

    public void Apply(Subst subst) {
        for (int i = 0; i < Count; i++) {
            constraints[i].Apply(subst);
        }
    }

    public bool Add(T t) {
        int idx = constraints.BinarySearch(t);
        if (idx >= 0)
            return false;
        constraints.Insert(~idx, t);
        return true;
    }

    public void Pop() => constraints.Pop();

    public override string ToString() =>
        Satisfied
            ? "\u22a4"
            : Violated
                ? "\u22a5"
                : string.Join(", ", constraints.Select(o => o.ToString()));

}