using StringBreaker.Constraints.ConstraintElement;
using StringBreaker.IntUtils;

namespace StringBreaker.Constraints.Modifier;

public class NumUnwindingModifier : ModifierBase {

    public Poly Num { get; }

    public NumUnwindingModifier(Poly num) => 
        Num = num;

    public override void Apply(NielsenNode node) {

        var c = node.MkChild(node, []);
        c.AddConstraints(new IntEq(Num.Clone())); // N1 == 0
        c.Parent!.SideConstraints.Add(new IntEq(Num.Clone()));

        c = node.MkChild(node, []);
        var sc = new Poly();
        sc.AddPoly(new Poly(1));
        sc.AddPoly(Num.Clone());
        c.AddConstraints(new IntLe(sc)); // 1 - N1 <= 0
        c.Parent!.SideConstraints.Add(new IntLe(sc.Clone()));
    }

    protected override int CompareToInternal(ModifierBase otherM) => 
        Num.CompareTo(((NumUnwindingModifier)otherM).Num);

    public override string ToString() => $"{Num} = 0 || {Num} > 0";
}