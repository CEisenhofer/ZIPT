using StringBreaker.Constraints.ConstraintElement;
using StringBreaker.IntUtils;
using StringBreaker.Tokens;
using StringBreaker.MiscUtils;

namespace StringBreaker.Constraints.Modifier;

public class PowerSplitModifier : DirectedNielsenModifier {
    public StrVarToken Var { get; }
    public PowerToken Power { get; }

    public PowerSplitModifier(StrVarToken var, PowerToken power, bool forward) : base(forward) {
        Var = var;
        Power = power;
    }

    public override void Apply(NielsenNode node) {
        // V / Base^Power' Base' && Power' < Power
        // V / Base^Power V

        IntVar newPow = new();
        var power = new PowerToken(Power.Base.Clone(), new Poly(newPow));
        var prefixes = Power.Base.GetPrefixes(Forwards);

        Str s;
        SubstVar subst;
        NielsenNode c;
        foreach (var p in prefixes) {
            s = new Str(power);
            s.AddRange(p.str, Forwards);
            subst = new SubstVar(Var, s);
            if (p.varDecomp is null)
                c = node.MkChild(node, [subst], true);
            else {
                subst = new SubstVar(Var, s.Apply(p.varDecomp));
                c = node.MkChild(node, [subst, p.varDecomp], true);
            }
            c.Apply(subst);
            c.AddConstraints(p.sideConstraints);
            c.Parent!.SideConstraints.AddRange(p.sideConstraints);
            c.AddConstraints(IntLe.MkLe(new Poly(0), new Poly(newPow)));
            c.Parent!.SideConstraints.Add(IntLe.MkLe(new Poly(0), new Poly(newPow)));
            c.AddConstraints(IntLe.MkLt(new Poly(newPow), Power.Power));
            c.Parent!.SideConstraints.Add(IntLe.MkLt(new Poly(newPow), Power.Power));
        }
        s = new Str(Var);
        s.Add(new PowerToken(Power.Base.Clone(), Power.Power.Clone()), Forwards);
        subst = new SubstVar(Var, s);
        c = node.MkChild(node, [subst], false);
        c.Apply(subst);
    }

    protected override int CompareToInternal(ModifierBase otherM) {
        PowerSplitModifier other = (PowerSplitModifier)otherM;
        int cmp = Power.CompareTo(other.Power);
        if (cmp != 0)
            return cmp;
        cmp = Var.CompareTo(other.Var);
        return cmp != 0 ? cmp : Forwards.CompareTo(other.Forwards);
    }

    public override string ToString() =>
        $"{Var} / ({Power.Base})^{{power}} [prefix({Power.Base})] && power < {Power.Power} \\/ {Var} / {(Forwards ? "" : Var + " ")}{Power}{(Forwards ? " " + Var : "")}";
}
