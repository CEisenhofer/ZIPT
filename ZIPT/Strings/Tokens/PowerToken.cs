using System.Diagnostics;
using Microsoft.Z3;
using ZIPT.MiscUtils;
using ZIPT.Constraints;
using ZIPT.Constraints.ConstraintElement;
using ZIPT.IntUtils;
using ZIPT.Strings;

namespace ZIPT.Strings.Tokens;

public sealed class PowerToken : StrToken {

    public Str Base { get; }
    public PDD<BigInteger> Power { get; }

    public PowerToken(Str b, PDD<BigInteger> power) {
        Base = b;
        Power = power;
        if (Base is [PowerToken p]) {
            Base = p.Base;
            Power = PDD.Mul(power, p.Power);
        }
    }

    public override bool IsNullable(NielsenNode node) => 
        Power.GetBounds(node).Max > 0 && Base.IsNullable(node);
        // !(0 < Power) && Base is nullable
        // !node.IsLt(new PDD(), Power) && Base.IsNullable(node);

    public override Expr ToExpr(NielsenGraph graph) =>
        graph.Env.PowerFct.Apply(Base.ToExpr(graph), Power.ToExpr(graph));

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