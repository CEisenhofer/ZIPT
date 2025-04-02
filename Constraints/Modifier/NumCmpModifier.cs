using System.Buffers;
using StringBreaker.Constraints.ConstraintElement;
using StringBreaker.IntUtils;

namespace StringBreaker.Constraints.Modifier;

public class NumCmpModifier : ModifierBase {

    public Poly N1 { get; }
    public Poly N2 { get; }

    public NumCmpModifier(Poly n1, Poly n2) {
        N1 = n1;
        N2 = n2;
    }

    public override void Apply(NielsenNode node) {
        // N1 < N2 (progress)
        // N2 <= N1 (progress)

        var c = node.MkChild(node, [], true);
        var sc = IntLe.MkLt(N1.Clone(), N2);
        c.AddConstraints(sc); // N1 < N2
        c.Parent!.SideConstraints.Add(sc.Clone());

        c = node.MkChild(node, [], true);
        sc = IntLe.MkLe(N2.Clone(), N1); // N2 <= N1
        c.AddConstraints(sc); // N2 - N1 <= 0 => N2 <= N1
        c.Parent!.SideConstraints.Add(sc.Clone());
    }

    protected override int CompareToInternal(ModifierBase otherM) {
        int cmp = N1.CompareTo(((NumCmpModifier)otherM).N1);
        return cmp != 0 ? cmp : N2.CompareTo(((NumCmpModifier)otherM).N2);
    }

    public override string ToString() => $"{N1} < {N2} || {N2} <= {N1}";
}