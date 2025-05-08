using StringBreaker.Constraints.ConstraintElement;
using StringBreaker.IntUtils;

namespace StringBreaker.Constraints.Modifier;

public abstract class NumUnwindingModifier : ModifierBase {

    public IntPoly Num { get; }

    public NumUnwindingModifier(IntPoly num) => 
        Num = num;

    public override void Apply(NielsenNode node) {

        node.MkChild(node, 
            Array.Empty<Subst>(),
            [new IntEq(Num.Clone())],
            Array.Empty<DisEq>(),
            true); // Num == 0


        node.MkChild(node,
            Array.Empty<Subst>(),
            [IntLe.MkLe(new IntPoly(1), Num)],
            Array.Empty<DisEq>(),
            false); // 1 <= Num
    }

    protected override int CompareToInternal(ModifierBase otherM) => 
        Num.CompareTo(((NumUnwindingModifier)otherM).Num);

    public override string ToString() => $"{Num} = 0 || 1 <= {Num}";
}

class ConstNumUnwindingModifier : NumUnwindingModifier {
    public ConstNumUnwindingModifier(IntPoly num) : base(num) { }
}

class VarNumUnwindingModifier : NumUnwindingModifier {
    public VarNumUnwindingModifier(IntPoly num) : base(num) { }
}