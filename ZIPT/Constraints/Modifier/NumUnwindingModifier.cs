using System.Numerics;
using ZIPT.Constraints.ConstraintElement;
using ZIPT.IntUtils;

namespace ZIPT.Constraints.Modifier;

public abstract class NumUnwindingModifier : ModifierBase {

    public PDD<BigInteger> Num { get; }

    protected NumUnwindingModifier(PDD<BigInteger> num, DependencyTracker reason) : base(reason) => 
        Num = num;

    // Unwinding for numeric variables: either Num == 0 or Num >= 1. Used for power unwinding.
    public override IEnumerable<NielsenEdge> Apply(LocalInfo info) {

        info.CurrentNode.MkChild(info,
            [], [],
            [new IntEq(Num, Reason)], [],
            true); // Num == 0
        yield return info.CurrentNode.Outgoing[^1];

        info.CurrentNode.MkChild(info,
            [], [],
            [IntLe.MkLe(info.Env.OneInt, Num, Reason)], [],
            false); // 1 <= Num
        yield return info.CurrentNode.Outgoing[^1];
    }

    protected override int CompareToInternal(ModifierBase otherM) => 
        Num.CompareTo(((NumUnwindingModifier)otherM).Num);

    public override string ToString() => $"{Num} = 0 || 1 <= {Num}";
}

class ConstNumUnwindingModifier : NumUnwindingModifier {
    // Specialized unwinding modifier for constant numerics.
    public ConstNumUnwindingModifier(PDD<BigInteger> num, DependencyTracker reason) : base(num, reason) { }
}

class VarNumUnwindingModifier : NumUnwindingModifier {
    // Specialized unwinding modifier for numeric variables.
    public VarNumUnwindingModifier(PDD<BigInteger> num, DependencyTracker reason) : base(num, reason) { }
}
