using System.Buffers;
using ZIPT.Constraints.ConstraintElement;
using ZIPT.IntUtils;

namespace ZIPT.Constraints.Modifier;

public class NumCmpModifier : ModifierBase {

    public IntPoly N1 { get; }
    public IntPoly N2 { get; }

    public NumCmpModifier(IntPoly n1, IntPoly n2) {
        N1 = n1;
        N2 = n2;
    }

    public override void Apply(NielsenNode node) {
        // N1 < N2 (progress)
        // N2 <= N1 (progress)

        node.MkChild(node, 
            Array.Empty<Subst>(),
            [IntLe.MkLt(N1.Clone(), N2)],
            Array.Empty<DisEq>(), true); // N1 < N2
        node.MkChild(node,
            Array.Empty<Subst>(),
            [IntLe.MkLe(N2.Clone(), N1)],
            Array.Empty<DisEq>(), true); // N2 <= N1
    }

    protected override int CompareToInternal(ModifierBase otherM) {
        int cmp = N1.CompareTo(((NumCmpModifier)otherM).N1);
        return cmp != 0 ? cmp : N2.CompareTo(((NumCmpModifier)otherM).N2);
    }

    public override string ToString() => $"{N1} < {N2} || {N2} <= {N1}";
}