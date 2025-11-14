using System.Numerics;
using ZIPT.Constraints.ConstraintElement;
using ZIPT.IntUtils;

namespace ZIPT.Constraints.Modifier;

public abstract class NumUnwindingModifier : ModifierBase {

    public PDD<BigInteger> Num { get; }

    protected NumUnwindingModifier(PDD<BigInteger> num) => 
        Num = num;

    public override IEnumerable<NielsenEdge> Apply(LocalInfo info) {

        info.CurrentNode.MkChild(info,
            [], [],
            [new IntEq(Num)], [],
            true); // Num == 0
        yield return info.CurrentNode.Outgoing[^1];

        info.CurrentNode.MkChild(info,
            [], [],
            [IntLe.MkLe(info.Env.OneInt, Num)], [],
            false); // 1 <= Num
        yield return info.CurrentNode.Outgoing[^1];
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