using System.Diagnostics;
using ZIPT.Constraints.ConstraintElement;
using ZIPT.Strings;
using ZIPT.Strings.Chunks;
using ZIPT.Strings.Tokens;

namespace ZIPT.Constraints.Modifier;

// Generalized power introduction: for each (x,base) case introduce substitutions of x
// by `base^{n}prefix` with a fresh power variable n and side constraints ensuring n >= 0.
// Generalized power-introduction modifier: introduces substitutions of a variable
// by `base^{n}prefix` with a fresh power variable `n` and appropriate side constraints.
public class GPowerIntrModifier : DirectedNielsenModifier {

    public List<(NamedStrToken x, Str val)> Cases { get; }

    public GPowerIntrModifier(List<(NamedStrToken x, Str val)> cases, bool forward, DependencyTracker reason) : base(forward, reason) {
        Debug.Assert(cases.Count > 0);
        Cases = cases;
    }

    public override IEnumerable<NielsenEdge> Apply(LocalInfo info) {
        foreach (var (v, @base) in Cases) {
            Debug.Assert(@base.Ground);
            var powerConstant = info.Env.IntPDDManager.MkPDD(v.GetPowerExtension());

            // TODO: If b = u^n => b = u
            Str b = StrEqBase.LcpCompressionFull(@base, info.Env) ?? @base;
            if (b.Length == 1 && b[true] is PowerToken pt)
                b = pt.Base; // aax... = x... => stronger x = a^n; the forms a^{2n} or (aa)^n are unnecessarily complicated

            var prefixes = StrManager.GetDecompose(info.CurrentNode, b, Forwards);
            var power = new PowerToken(b, powerConstant);

            foreach (var p in prefixes) {
                Str s = info.Env.StrManager.Concat(info.Env.MkString(power), p.Prefix, Forwards);
                var subst = new Subst(v, s);
                Debug.Assert(p.VarDecomp is null);
                Constraint[] cnstr = new Constraint[p.SideConstraints.Count + 1];
                for (int i = 0; i < p.SideConstraints.Count; i++) {
                    cnstr[i] = p.SideConstraints[i];
                }
                cnstr[^1] = IntLe.MkLe(info.Env.ZeroInt, powerConstant, Reason);
                info.CurrentNode.MkChild(info, [subst], [], cnstr, [], true);
                yield return info.CurrentNode.Outgoing[^1];
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
        {
            var @base = o.val.ToString();
            if (@base.Length == 1)
                return $"{o.x} / {o.val}^{{{o.x.GetPowerExtension()}}} [prefix({o.val})]";
            return $"{o.x} / ({o.val})^{{{o.x.GetPowerExtension()}}} [prefix({o.val})]";
        }));
}