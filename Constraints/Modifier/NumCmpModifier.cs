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

        var c = node.MkChild(node, []);
        var sc = new Poly();
        sc.AddPoly(N1.Clone());
        sc.SubPoly(N2.Clone());
        sc.SubPoly(new Poly(1));
        c.AddConstraints(new IntLe(sc)); // N1 - N2 - 1 <= 0 => N1 <= N2 + 1
        c.Parent!.SideConstraints.Add(new IntLe(sc.Clone()));

        c = node.MkChild(node, []);
        sc = new Poly();
        sc.AddPoly(N2.Clone());
        sc.SubPoly(N1.Clone());
        c.AddConstraints(new IntLe(sc)); // N2 - N1 <= 0 => N2 <= N1
        c.Parent!.SideConstraints.Add(new IntLe(sc.Clone()));
    }

    protected override int CompareToInternal(ModifierBase otherM) {
        int cmp = N1.CompareTo(((NumCmpModifier)otherM).N1);
        return cmp != 0 ? cmp : N2.CompareTo(((NumCmpModifier)otherM).N2);
    }

    public override string ToString() => $"{N1} < {N2} || {N2} <= {N1}";
}