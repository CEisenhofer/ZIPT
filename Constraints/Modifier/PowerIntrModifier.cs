using StringBreaker.Constraints.ConstraintElement;
using StringBreaker.IntUtils;
using StringBreaker.Tokens;
using System.Diagnostics;
using StringBreaker.MiscUtils;

namespace StringBreaker.Constraints.Modifier;

public class PowerIntrModifier : DirectedNielsenModifier {
    public StrVarToken Var { get; }
    public Str Base { get; }
    public Poly Power { get; }

    public PowerIntrModifier(StrVarToken var, Str @base, bool backward) : base(backward) {
        Debug.Assert(!@base.Ground);
        Var = var;
        Base = @base;
        Power = new Poly(Var.GetPowerExtension());
    }

    public override void Apply(NielsenNode node) {
        // V1 / Base^Power Base'
        // To avoid repeatedly making 0-step power introductions, we explicitly make the split on 0 and > 0 repetitions
        // e.g., xy = yx => x / (y'y'')^n y' && y = y'y'' && |y'| < |y|
        //       (y'y'')^n y'y'y'' = y'y''(y'y'')^n y' && 0 < |y''|
        //       y'y'' = y''y' && 0 < |y''|
        // Nothing prevents us from splitting on y' / (y'')^m y''' now

        var power = new PowerToken(Base, Power);
        var prefixes = Base.GetPrefixes();

        foreach (var p in prefixes) {
            Str s = new Str(power);
            s.AddRange(p.str, Backwards);
            var subst = new Subst(Var, s);
            NielsenNode c;
            if (p.varDecomp is null)
                c = node.MkChild(node, [subst]);
            else {
                subst = new Subst(Var, s.Apply(p.varDecomp));
                c = node.MkChild(node, [subst, p.varDecomp]);
            }
            foreach (var cnstr in c.AllStrConstraints) {
                cnstr.Apply(subst);
            }
            c.AddConstraints(p.sideConstraints);
            c.Parent!.SideConstraints.AddRange(p.sideConstraints);
            var lowerBound = new Poly();
            lowerBound.SubPoly(Power);
            c.AddConstraints(new IntLe(lowerBound)); // -Power <= 0 => Power >= 0
            c.Parent!.SideConstraints.Add(new IntLe(lowerBound));
        }
    }

    protected override int CompareToInternal(ModifierBase otherM) {
        GPowerIntrModifier other = (GPowerIntrModifier)otherM;
        int cmp = Base.Count.CompareTo(other.Base.Count); // TODO: Get a better heuristic (power nesting, variables in powers, ...)
        if (cmp != 0)
            return cmp;
        cmp = Backwards.CompareTo(other.Backwards);
        return cmp != 0 ? cmp : Var.CompareTo(other.Var);
    }

    public override string ToString() =>
        $"{Var} / {Base}^{{{Power}}} [prefix({Base})]";
}

class GPowerGPowerIntrModifier : CombinedModifier {
    public GPowerGPowerIntrModifier(StrVarToken v1, StrVarToken v2, Str p1, Str p2, bool backward) : base(
        new GPowerIntrModifier(v1, p1, backward),
        new GPowerIntrModifier(v2, p2, backward)) { }
}

class GPowerPowerIntrModifier : CombinedModifier {
    public GPowerPowerIntrModifier(StrVarToken v1, StrVarToken v2, Str p1, Str p2, bool backward) : base(
        new GPowerIntrModifier(v1, p1, backward),
        new PowerIntrModifier(v2, p2, backward)) { }
}

class PowerPowerIntrModifier : CombinedModifier {
    public PowerPowerIntrModifier(StrVarToken v1, StrVarToken v2, Str p1, Str p2, bool backward) : base(
        new PowerIntrModifier(v1, p1, backward),
        new PowerIntrModifier(v2, p2, backward)) { }
}

class GPowerIntrConstNielsen : CombinedModifier {
    public GPowerIntrConstNielsen(StrVarToken v1, StrVarToken v2, Str p, bool backward) : base(
        new GPowerIntrModifier(v1, p, backward),
        new ConstNielsenModifier(v2, v1, backward)) { }
}

class PowerIntrConstNielsen : CombinedModifier {
    public PowerIntrConstNielsen(StrVarToken v1, StrVarToken v2, Str p, bool backward) : base(
        new PowerIntrModifier(v1, p, backward),
        new ConstNielsenModifier(v2, v1, backward)) { }
}