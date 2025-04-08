using StringBreaker.Constraints.ConstraintElement;
using StringBreaker.Strings.Tokens;

namespace StringBreaker.Constraints.Modifier;

public class PowerEpsilonModifier : ModifierBase {

    public PowerToken Power { get; }

    public PowerEpsilonModifier(PowerToken power) => Power = power;

    public override void Apply(NielsenContext ctx) {
        // Power.Power = 0 (progress)
        // Power.Base / "" (progress)
        var c = ctx.CurrentNode.MkChild(ctx, [], true);
        c.AddConstraints(new IntEq(Power.Power.Clone()));
        c.Parent!.SideConstraints.Add(new IntEq(Power.Power.Clone()));
        c = ctx.CurrentNode.MkChild(ctx, [], true);
        c.AddConstraints(new StrEq(Power.Base));
        c.Parent!.SideConstraints.Add(new StrEq(Power.Base));
    }

    protected override int CompareToInternal(ModifierBase otherM) => 
        Power.CompareTo(((PowerEpsilonModifier)otherM).Power);

    public override string ToString() => $"{Power.Power} = 0 || {Power.Base} = ε";
}