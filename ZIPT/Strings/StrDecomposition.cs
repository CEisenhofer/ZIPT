using System.Text;
using ZIPT.Constraints;
using ZIPT.Constraints.ConstraintElement;
using ZIPT.Strings.Chunks;

namespace ZIPT.Strings;

public class StrDecomposition {
    public Str Prefix { get; set; }
    public Str Postfix { get; set; }
    public readonly List<IntConstraint> SideConstraints;
    public readonly Subst? VarDecomp;

    public StrDecomposition(Str prefix, Str postfix, List<IntConstraint> sideConstraints, Subst? varDecomp) {
        Prefix = prefix;
        Postfix = postfix;
        SideConstraints = sideConstraints;
        VarDecomp = varDecomp;
    }

    public override string ToString() {
        StringBuilder sb = new();
        sb.Append(Prefix).Append("; ").Append(Postfix);
        if (SideConstraints.Count > 0) {
            foreach (var sc in SideConstraints) {
                sb.Append("; ").Append(sc);
            }
        }
        if (VarDecomp.HasValue)
            sb.Append("; ").Append(VarDecomp);
        return sb.ToString();
    }
}