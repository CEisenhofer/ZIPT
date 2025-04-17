using System.Diagnostics;
using Microsoft.Z3;
using StringBreaker.Constraints;
using StringBreaker.Constraints.ConstraintElement;
using StringBreaker.IntUtils;
using StringBreaker.MiscUtils;

namespace StringBreaker.Tokens;

public sealed class PowerToken : StrToken {

    public Str Base { get; }
    public Poly Power { get; }

    public PowerToken(Str b, Poly power) {
        Base = b;
        Power = power;
        if (Base is [PowerToken p]) {
            Base = p.Base;
            Power = Poly.Mul(power, p.Power);
        }
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
        graph.Cache.PowerFct.Apply(Base.ToExpr(graph), Power.ToExpr(graph));

    public override bool RecursiveIn(NamedStrToken v) =>
        Base.RecursiveIn(v);

    protected override int CompareToInternal(StrToken other) {
        int cmp = Base.CompareTo(((PowerToken)other).Base);
        return cmp != 0 ? cmp : Power.CompareTo(((PowerToken)other).Power);
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