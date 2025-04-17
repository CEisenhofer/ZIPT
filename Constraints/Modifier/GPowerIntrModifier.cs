using System.Diagnostics;
using StringBreaker.Constraints.ConstraintElement;
using StringBreaker.IntUtils;
using StringBreaker.MiscUtils;
using StringBreaker.Tokens;

namespace StringBreaker.Constraints.Modifier;

public class GPowerIntrModifier : DirectedNielsenModifier {

    public List<(NamedStrToken x, Str val)> Cases { get; }

    public GPowerIntrModifier(List<(NamedStrToken x, Str val)> cases, bool forward) : base(forward) {
        Debug.Assert(cases.IsNonEmpty());
        Cases = cases;
    }

    public override void Apply(NielsenNode node) {
        // V_i / Base_i^powerConstant Base' with Base' being a syntactic prefix of Base (progress)
        foreach (var (v, @base) in Cases) {
            Debug.Assert(@base.Ground);
            var powerConstant = new Poly(v.GetPowerExtension());

            Str b = StrEqBase.LcpCompressionFull(@base) ?? @base;

            var prefixes = b.GetPrefixes(Forwards);
            var power = new PowerToken(b, powerConstant);

            foreach (var p in prefixes) {
                Str s = new Str(power);
                s.AddRange(p.str, !Forwards);
                var subst = new SubstVar(v, s);
                Debug.Assert(p.varDecomp is null);
                var c = node.MkChild(node, [subst], true);
                c.Apply(subst);
                c.AddConstraints(p.sideConstraints);
                c.Parent!.SideConstraints.AddRange(p.sideConstraints);
                var lowerBound = new Poly();
                lowerBound.Sub(powerConstant);
                c.AddConstraints(new IntLe(lowerBound)); // -Power <= 0 => Power >= 0
                c.Parent!.SideConstraints.Add(new IntLe(lowerBound));
            }
        }
    }

    protected override int CompareToInternal(ModifierBase otherM) {
        GPowerIntrModifier other = (GPowerIntrModifier)otherM;
        int cmp = Cases.Count.CompareTo(other.Cases.Count); // TODO: Get a better heuristic (power nesting, variables in powers, ...)
        if (cmp != 0)
            return cmp;
        for (int i = 0; i < other.Cases.Count; i++) {
            cmp = Cases[i].val.CompareTo(other.Cases[i].val);
            if (cmp != 0)
                return cmp;
            cmp = Cases[i].x.CompareTo(other.Cases[i].x);
            if (cmp != 0)
                return cmp;
        }
        return Forwards.CompareTo(other.Forwards);
    }

    public override string ToString() =>
        string.Join(" || ", Cases.Select(o => 
            $"{o.x} / ({o.val})^{{{o.x.GetPowerExtension()}}} [prefix({o.val})]"));
}