using System.Collections.Generic;
using System.Diagnostics;
using StringBreaker.Constraints.ConstraintElement;
using StringBreaker.IntUtils;
using StringBreaker.MiscUtils;
using StringBreaker.Tokens;

namespace StringBreaker.Constraints.Modifier;

public class GPowerIntrModifier : DirectedNielsenModifier {

    public StrVarToken Var { get; }
    public Str Base { get; }
    public Poly Power { get; }

    public GPowerIntrModifier(StrVarToken var, Str @base, bool backward) : base(backward) {
        Debug.Assert(@base.Ground);
        Var = var;
        Base = @base;
        Power = new Poly(Var.GetPowerExtension());
    }

    public override void Apply(NielsenNode node) {
        // V1 / Base^Power Base' with Base' being a syntactic prefix of Base

        var power = new PowerToken(Base, Power);
        var prefixes = Base.GetPrefixes();
        
        foreach (var p in prefixes) {
            Str s = new Str(power);
            s.AddRange(p.str, Backwards);
            var subst = new Subst(Var, s);
            Debug.Assert(p.varDecomp is null);
            var c = node.MkChild(node, [subst]);
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