using System.Diagnostics;
using ZIPT.MiscUtils;
using ZIPT.Constraints.ConstraintElement;
using ZIPT.IntUtils;
using ZIPT.Tokens;

namespace ZIPT.Constraints.Modifier;

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
            var powerConstant = new IntPoly(v.GetPowerExtension());

            // TODO: If b = u^n => b = u
            Str b = StrEqBase.LcpCompressionFull(@base) ?? @base;
            if (b.Count == 1 && b.Peek(true) is PowerToken pt)
                b = pt.Base; // aax... = x... => stronger x = a^n; the forms a^{2n} or (aa)^n are unnecessarily complicated

            var prefixes = b.GetPrefixes(Forwards);
            var power = new PowerToken(b, powerConstant);

            foreach (var p in prefixes) {
                Str s = new Str(power);
                s.AddRange(p.str, !Forwards);
                var subst = new SubstVar(v, s);
                Debug.Assert(p.varDecomp is null);
                Constraint[] cnstr = new Constraint[p.sideConstraints.Count + 1];
                for (int i = 0; i < p.sideConstraints.Count; i++) {
                    cnstr[i] = p.sideConstraints[i];
                }
                cnstr[^1] = IntLe.MkLe(new IntPoly(), new IntPoly(powerConstant));
                node.MkChild(node, [subst], cnstr, Array.Empty<DisEq>(), true);
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