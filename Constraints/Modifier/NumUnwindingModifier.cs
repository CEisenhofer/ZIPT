using StringBreaker.Constraints.ConstraintElement;
using StringBreaker.IntUtils;

namespace StringBreaker.Constraints.Modifier;

public abstract class NumUnwindingModifier : ModifierBase {

    public Poly Num { get; }

    public NumUnwindingModifier(Poly num) => 
        Num = num;

    public override void Apply(NielsenNode node) {

        var c = node.MkChild(node, [], true);
        c.AddConstraints(new IntEq(Num.Clone())); // N1 == 0
        c.Parent!.SideConstraints.Add(new IntEq(Num.Clone()));

        c = node.MkChild(node, [], false); // TODO: Maybe also true?
        var sc = IntLe.MkLe(new Poly(1), Num.Clone());
        c.AddConstraints(sc); // 1 <= N1
        c.Parent!.SideConstraints.Add(sc.Clone());
    }

    protected override int CompareToInternal(ModifierBase otherM) => 
        Num.CompareTo(((NumUnwindingModifier)otherM).Num);

    public override string ToString() => $"{Num} = 0 || 1 <= {Num}";
}

class ConstNumUnwindingModifier : NumUnwindingModifier {
    public ConstNumUnwindingModifier(Poly num) : base(num) { }
}

class VarNumUnwindingModifier : NumUnwindingModifier {
    public VarNumUnwindingModifier(Poly num) : base(num) { }
}