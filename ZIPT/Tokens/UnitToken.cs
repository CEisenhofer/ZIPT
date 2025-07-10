using System.Diagnostics;
using Microsoft.Z3;
using ZIPT.Constraints;
using ZIPT.Constraints.ConstraintElement;

namespace ZIPT.Tokens;

public abstract class UnitToken : StrToken {

    public sealed override bool Ground => true;
    public sealed override bool IsNullable(NielsenNode node) => false;

    public sealed override List<(IStr str, List<IntConstraint> sideConstraints, Subst? varDecomp)> GetPrefixes(bool dir) =>
        // P(a) := {}
        [([], [], null)];
}