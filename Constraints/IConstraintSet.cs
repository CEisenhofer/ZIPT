using StringBreaker.Constraints.ConstraintElement;
using StringBreaker.Strings;
using StringBreaker.Tokens;

namespace StringBreaker.Constraints;

public interface IConstraintSet {
    bool Satisfied { get; }
    bool Violated { get; }
    int Count { get; }

    IEnumerable<Constraint> EnumerateBaseConstraints();
    void Apply(Subst subst);
    bool Remove(Constraint constraint);
    void RemoveAt(int idx);
    int GetHashCode();
}