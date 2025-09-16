using ZIPT.Constraints;
using ZIPT.Constraints.ConstraintElement;
using ZIPT.Strings.Chunks;

namespace ZIPT.Strings;

public class PrefixDecomposition {
    public Str Str { get; set; }
    public readonly List<IntConstraint> SideConstraints;
    public readonly Subst? VarDecomp;

    public PrefixDecomposition(Str str, List<IntConstraint> sideConstraints, Subst? varDecomp) {
        Str = str;
        SideConstraints = sideConstraints;
        VarDecomp = varDecomp;
    }
}