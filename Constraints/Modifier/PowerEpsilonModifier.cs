using ZIPT.Constraints.ConstraintElement;
using ZIPT.Tokens;

namespace ZIPT.Constraints.Modifier;

public class PowerEpsilonModifier : ModifierBase {

    public PowerToken Power { get; }

    public PowerEpsilonModifier(PowerToken power) => Power = power;

    public override void Apply(NielsenNode node) {
        // Power.Power = 0 (progress)
        // Power.Base / "" (progress)
        node.MkChild(node, 
            Array.Empty<Subst>(),
            [new IntEq(Power.Power.Clone())],
            Array.Empty<DisEq>(), true);
        node.MkChild(node, 
            Array.Empty<Subst>(),
            [new StrEq(Power.Base)],
            Array.Empty<DisEq>(), true);
    }

    protected override int CompareToInternal(ModifierBase otherM) => 
        Power.CompareTo(((PowerEpsilonModifier)otherM).Power);

    public override string ToString() => $"{Power.Power} = 0 || {Power.Base} = ε";
}