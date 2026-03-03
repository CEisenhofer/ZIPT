using ZIPT.Constraints.ConstraintElement;
using ZIPT.Strings.Tokens;

namespace ZIPT.Constraints.Modifier;

// Offer two progress choices when a power could be epsilon: either set its exponent to 0
// or equate its base to the empty string (both produce child nodes).
public class PowerEpsilonModifier : ModifierBase {

    public PowerToken Power { get; }

    public PowerEpsilonModifier(PowerToken power, DependencyTracker reason) : base(reason) => Power = power;

    public override IEnumerable<NielsenEdge> Apply(LocalInfo info) {
        info.CurrentNode.MkChild(info, 
            [], [],
            [new IntEq(Power.Power, Reason)], [],
            true);
        yield return info.CurrentNode.Outgoing[^1];

        info.CurrentNode.MkChild(info, 
            [], [],
            [new StrEq(Power.Base, info.Env.EmptyStr, Reason)], [],
            true);
        yield return info.CurrentNode.Outgoing[^1];
    }

    protected override int CompareToInternal(ModifierBase otherM) => 
        Power.CompareTo(((PowerEpsilonModifier)otherM).Power);

    public override string ToString() => $"{Power.Power} = 0 || {Power.Base} = ε";
}
