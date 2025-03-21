using System.Diagnostics;
using System.Text;
using Microsoft.Z3;
using StringBreaker.Constraints;
using StringBreaker.Constraints.ConstraintElement;
using StringBreaker.IntUtils;
using StringBreaker.MiscUtils;

namespace StringBreaker.Tokens;

public sealed class PowerToken : StrToken {

    // a(ba)^n b = (ab)^m

    // Do not alter the _content_ of those variables (tokens are immutable)

    // least repeated prefix (lrp) used. e.g., (ab)^2mn instead of ((abab)^n)^m
    // Note that (abab)^n is normalized (ab)^2n but (ababc)^n stays the same, as we cannot compress the whole body
    // Further, ((ab)^m ab (ab)^n)^k becomes (ab)^{(1 + m + n)k}
    // (a(ba)^m b)^n should also become (ab)^{(m + 1)n}
    // If variables are involved, it is hard to determine the lrp
    // TODO: Implement the non-trivial cases
    // TODO: Sometimes it works even though variables are involved. (axb)^n is normalized iff x != (ba)^m
    bool Normalized { get; }
    public Str Base { get; }
    public Poly Power { get; }

    public PowerToken(Str b, Poly power) {
        Base = b;
        Power = power;
        if (Base is [PowerToken p])
            Power = Poly.Mul(power, p.Power);
        if (Base.All(o => o is CharToken)) {
            Debug.Assert(Base.Count > 0);
            string lrp = StringUtils.LeastRepeatedPrefix(
                new string(Base.OfType<CharToken>().Select(o => o.Value).ToArray()));
            Debug.Assert(lrp.Length > 0);
            int m = Base.Count / lrp.Length;
            Debug.Assert(Base.Count % lrp.Length == 0);
            Debug.Assert(m >= 1);
            if (m > 1) {
                Power = Poly.Mul(Power, new Poly(m));
                Base = new Str(lrp.Select(o => (StrToken)new CharToken(o)).ToArray());
            }
            Normalized = true;
        }
        else
            Normalized = false;
    }

    
    public override bool Ground => Base.Ground;

    public override bool IsNullable(NielsenNode node) => 
        Power.GetBounds(node).Max > 0 && Base.IsNullable(node);
        // !(0 < Power) && Base is nullable
        // !node.IsLt(new Poly(), Power) && Base.IsNullable(node);

    public override Str Apply(Subst subst) {
        var @base = Base.Apply(subst);
        if (@base.IsEmpty())
            return [];
        return [new PowerToken(@base, Power)];
    }

    public override Str Apply(Interpretation itp) {
        var @base = Base.Apply(itp);
        if (@base.IsEmpty())
            return [];
        var p = Power.Apply(itp);
        if (!p.IsConst(out var val) || val > Options.ModelUnwindingBound) 
            return [new PowerToken(@base, p)];
        Debug.Assert(!val.IsNeg);
        if (!val.IsPos)
            return [];
        Str result = [];
        for (int i = 0; i < val; i++) {
            result.AddLastRange(@base);
        }
        return result;
    }

    public override List<(Str str, List<IntConstraint> sideConstraints, Subst? varDecomp)> GetPrefixes(bool dir) {
        // P(u^n) := u^m P(u) with 0 <= m < n
        IntVar m = new();
        PowerToken token = new PowerToken(Base, new Poly(m));
        IntLe leastZero = new IntLe(new Poly(0), new Poly(m));
        IntLe lessThanPower = IntLe.MkLt(new Poly(m), Power);

        var prefixes = Base.GetPrefixes(dir);

        for (int i = 0; i < prefixes.Count; i++) {
            prefixes[i].str.Add(token, dir);
            prefixes[i].sideConstraints.Add(leastZero.Clone());
            prefixes[i].sideConstraints.Add(lessThanPower.Clone());
        }

        return prefixes;
    }

    public override Expr ToExpr(NielsenGraph graph) =>
        graph.Propagator.PowerFct.Apply(Base.ToExpr(graph), Power.ToExpr(graph));

    public override bool RecursiveIn(StrVarToken v) =>
        Base.RecursiveIn(v);

    protected override int CompareToInternal(StrToken other) {
        int cmp = Base.CompareTo(((PowerToken)other).Base);
        if (cmp != 0)
            return cmp;
        return Power.CompareTo(((PowerToken)other).Power);
    }

    public override bool Equals(StrToken? other) =>
        other is PowerToken token && Equals(token);

    public bool Equals(PowerToken other) =>
        Base.Equals(other.Base) && Power.Equals(other.Power);

    public override int GetHashCode() => 495035077 * Base.GetHashCode() + 273877411 * Power.GetHashCode();

    public override string ToString(NielsenGraph? graph) {
        string b = Base.ToString(graph);
        return b.Length == 1 ? $"{b}^{{{Power}}}" : $"({b})^{{{Power}}}";
    }

}