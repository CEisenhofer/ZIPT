using System.Numerics;
using ZIPT.Constraints.ConstraintElement;
using ZIPT.IntUtils;

namespace ZIPT.Constraints.Modifier;

public abstract class NumUnwindingModifier : ModifierBase {

    public PDD<BigInteger> Num { get; }

    public NumUnwindingModifier(PDD<BigInteger> num) => 
        Num = num;

    public override IEnumerable<NielsenEdge> Apply(NielsenNode node) {

        node.MkChild(node,
            Array.Empty<Subst>(),
            [new IntEq(Num)], [],
            true); // Num == 0
        yield return node.Outgoing[^1];

        node.MkChild(node,
            Array.Empty<Subst>(),
            [IntLe.MkLe(node.Env.OneInt, Num)], [],
            false); // 1 <= Num
        yield return node.Outgoing[^1];
    }

    protected override int CompareToInternal(ModifierBase otherM) => 
        Num.CompareTo(((NumUnwindingModifier)otherM).Num);

    public override string ToString() => $"{Num} = 0 || 1 <= {Num}";
}

class ConstNumUnwindingModifier : NumUnwindingModifier {
    public ConstNumUnwindingModifier(PDD<BigInteger> num) : base(num) { }
}

class VarNumUnwindingModifier : NumUnwindingModifier {
    public VarNumUnwindingModifier(PDD<BigInteger> num) : base(num) { }
}