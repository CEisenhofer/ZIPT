using StringBreaker.Constraints.ConstraintElement;
using StringBreaker.IntUtils;
using StringBreaker.Tokens;
using System.Diagnostics;
using StringBreaker.MiscUtils;

namespace StringBreaker.Constraints.Modifier;

// We might want to drop this or change it to an easier form
public class PowerIntrModifier : DirectedNielsenModifier {
    public StrVarToken Var { get; }
    public Str Base { get; }
    public Poly Power { get; }

    public PowerIntrModifier(StrVarToken var, Str @base, bool forward) : base(forward) {
        throw new NotSupportedException(); // For now, let's not use this
        // Better: x / u^n x && |x| < |u| (this avoids another power introduction on x)
        // However, non ground powers are super annoying to deal with
        Debug.Assert(!@base.Ground);
        Var = var;
        Base = @base;
        Power = new Poly(Var.GetPowerExtension());
    }

    public override void Apply(NielsenNode node) {
        // V1 / Base^Power Base'
        // To avoid repeatedly making 0-step power introductions, we explicitly make the split on 0 and > 0 repetitions
        // e.g., xy = yx => x / (y'y'')^n y' && y = y'y'' && |y'| < |y|
        //       (y'y'')^n y'y''y'y'' = y'y''(y'y'')^n y'y'' && 0 < |y''|
        //       y'y'' = y''y' && 0 < |y''|
        // Nothing prevents us from splitting on y' / (y'')^m y''' now

        var power = new PowerToken(Base, Power);
        var prefixes = Base.GetPrefixes(Forwards);

        foreach (var p in prefixes) {
            Str s = new Str(power);
            s.AddRange(p.str, Forwards);
            var subst = new SubstVar(Var, s);
            NielsenNode c;
            if (p.varDecomp is null)
                c = node.MkChild(node, [subst], false);
            else {
                subst = new SubstVar(Var, s.Apply(p.varDecomp));
                c = node.MkChild(node, [subst, p.varDecomp], false);
            }
            c.Apply(subst);
            c.AddConstraints(p.sideConstraints);
            c.Parent!.SideConstraints.AddRange(p.sideConstraints);
            var lowerBound = new Poly();
            lowerBound.Sub(Power);
            c.AddConstraints(new IntLe(lowerBound)); // -Power <= 0 => Power >= 0
            c.Parent!.SideConstraints.Add(new IntLe(lowerBound));
        }
    }

    protected override int CompareToInternal(ModifierBase otherM) {
        PowerIntrModifier other = (PowerIntrModifier)otherM;
        int cmp = Base.Count.CompareTo(other.Base.Count); // TODO: Get a better heuristic (power nesting, variables in powers, ...)
        if (cmp != 0)
            return cmp;
        cmp = Forwards.CompareTo(other.Forwards);
        return cmp != 0 ? cmp : Var.CompareTo(other.Var);
    }

    public override string ToString() =>
        $"{Var} / {Base}^{{{Power}}} [prefix({Base})]";
}
