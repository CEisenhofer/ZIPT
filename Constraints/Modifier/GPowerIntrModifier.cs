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

    public GPowerIntrModifier(StrVarToken var, Str @base, bool forward) : base(forward) {
        Debug.Assert(@base.Ground);
        Var = var;
        Base = @base;
    }

    public override void Apply(NielsenNode node) {
        // V1 / Base^powerConstant Base' with Base' being a syntactic prefix of Base
        var powerConstant = new Poly(Var.GetPowerExtension());

        var b = Base;

        if (Base.All(o => o is UnitToken)) {
            Debug.Assert(Base.Count > 0);
            int lrpLen = StringUtils.LeastRepeatedPrefix(Base);
            Debug.Assert(lrpLen > 0 && lrpLen <= Base.Count);
            // TODO: Improve
            while (Base.Count > lrpLen) {
                Base.DropLast();
            }
            b = Base;
        }
        else
            b = StrEqBase.LcpCompression(Base) ?? Base;

        var power = new PowerToken(b, powerConstant);
        var prefixes = Base.GetPrefixes(Forwards);
        
        foreach (var p in prefixes) {
            Str s = new Str(power);
            s.AddRange(p.str, !Forwards);
            var subst = new SubstVar(Var, s);
            Debug.Assert(p.varDecomp is null);
            var c = node.MkChild(node, [subst]);
            c.Apply(subst);
            c.AddConstraints(p.sideConstraints);
            c.Parent!.SideConstraints.AddRange(p.sideConstraints);
            var lowerBound = new Poly();
            lowerBound.Sub(powerConstant);
            c.AddConstraints(new IntLe(lowerBound)); // -Power <= 0 => Power >= 0
            c.Parent!.SideConstraints.Add(new IntLe(lowerBound));
        }
    }

    protected override int CompareToInternal(ModifierBase otherM) {
        GPowerIntrModifier other = (GPowerIntrModifier)otherM;
        int cmp = Base.Count.CompareTo(other.Base.Count); // TODO: Get a better heuristic (power nesting, variables in powers, ...)
        if (cmp != 0)
            return cmp;
        cmp = Forwards.CompareTo(other.Forwards);
        return cmp != 0 ? cmp : Var.CompareTo(other.Var);
    }

    public override string ToString() =>
        $"{Var} / {Base}^{{{Var.GetPowerExtension()}}} [prefix({Base})]";
}