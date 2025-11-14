using ZIPT.Constraints.ConstraintElement;
using ZIPT.Strings.Tokens;

namespace ZIPT.Constraints.Modifier;

public class PowerEpsilonModifier : ModifierBase {

    public PowerToken Power { get; }

    public PowerEpsilonModifier(PowerToken power) => Power = power;

    public override IEnumerable<NielsenEdge> Apply(LocalInfo info) {
        // Power.Power = 0 (progress)
        // Power.Base / "" (progress)
        info.CurrentNode.MkChild(info, 
            [], [],
            [new IntEq(Power.Power)], [],
            true);
        yield return info.CurrentNode.Outgoing[^1];

        info.CurrentNode.MkChild(info, 
            [], [],
            [new StrEq(Power.Base, info.Env.EmptyStr)], [],
            true);
        yield return info.CurrentNode.Outgoing[^1];
    }

    protected override int CompareToInternal(ModifierBase otherM) => 
        Power.CompareTo(((PowerEpsilonModifier)otherM).Power);

    public override string ToString() => $"{Power.Power} = 0 || {Power.Base} = ε";
}