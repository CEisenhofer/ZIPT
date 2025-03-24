using System.Diagnostics;
using Microsoft.Z3;
using StringBreaker.Constraints;
using StringBreaker.Constraints.ConstraintElement;

namespace StringBreaker.Tokens;

public abstract class UnitToken : StrToken {

    public sealed override bool Ground => true;
    public sealed override bool IsNullable(NielsenNode node) => false;

    public sealed override List<(Str str, List<IntConstraint> sideConstraints, Subst? varDecomp)> GetPrefixes(bool dir) =>
        // P(a) := {}
        [([], [], null)];

    public sealed override bool RecursiveIn(NamedStrToken v) => false;
}