using StringBreaker.Constraints.ConstraintElement;
using StringBreaker.Tokens;

namespace StringBreaker.Constraints.Modifier;

public class PowerEpsilonModifier : ModifierBase {

    public PowerToken Power { get; }

    public PowerEpsilonModifier(PowerToken power) => Power = power;

    public override void Apply(NielsenNode node) {
        // Power.Power = 0 (progress)
        // Power.Base / "" (progress)
        var c = node.MkChild(node, [], true);
        c.AddConstraints(new IntEq(Power.Power.Clone()));
        c.Parent!.SideConstraints.Add(new IntEq(Power.Power.Clone()));
        c = node.MkChild(node, [], true);
        c.AddConstraints(new StrEq(Power.Base));
        c.Parent!.SideConstraints.Add(new StrEq(Power.Base));
    }

    protected override int CompareToInternal(ModifierBase otherM) => 
        Power.CompareTo(((PowerEpsilonModifier)otherM).Power);

    public override string ToString() => $"{Power.Power} = 0 || {Power.Base} = ε";
}