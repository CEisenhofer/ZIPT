using System.Diagnostics;
using System.Numerics;
using System.Runtime.Intrinsics.X86;
using Microsoft.Z3;
using ZIPT.MiscUtils;
using ZIPT.Constraints;
using ZIPT.Constraints.ConstraintElement;
using ZIPT.IntUtils;
using ZIPT.Strings;
using ZIPT.Strings.Chunks;

namespace ZIPT.Strings.Tokens;

public sealed class PowerToken : StrToken {

    public Str Base { get; }
    public PDD<BigInteger> Power { get; }

    public bool Ground => Base.Ground;

    public PowerToken(Str b, PDD<BigInteger> power) {
        Base = b;
        Power = power;
        if (Base.Length == 1 && Base[0] is PowerToken p) {
            Base = p.Base;
            Power = power.Mul(p.Power);
        }
    }

    public static Str MkPower(Str b, PDD<BigInteger> power, Environment env) {
        if (power.IsZero)
            return env.EmptyStr;
        if (power.IsOne)
            return b;
        return env.MkString(new PowerToken(b, power));
    }

    // TODO: Check
    public override bool IsNullable(NielsenNode node) => 
        Power.GetBounds(node).Max.IsPos && StrManager.IsNullable(node, Base);
    // !(0 < Power) && Base is nullable
    // !node.IsLt(node.Env.ZeroInt, Power) && Base.IsNullable(node);

    public override List<PrefixDecomposition> GetPrefixes(NielsenNode node, bool fwd) {
        // P(u^n) := u^m P(u) with 0 <= m < n
        IntVar m = new();
        var newExponent = node.Env.IntPDDManager.MkPDD(m);
        PowerToken newPowerToken = new PowerToken(Base, newExponent);
        Str newStr = node.Env.MkString(newPowerToken);
        IntLe leastZero = new IntLe(node.Env.ZeroInt, newExponent);
        IntLe lessThanPower = IntLe.MkLt(newExponent, Power);

        var prefixes = StrManager.GetPrefixes(node, Base, fwd);

        for (int i = 0; i < prefixes.Count; i++) {
            if (fwd)
                prefixes[i].Str = node.Env.StrManager.Concat(prefixes[i].Str, newStr);
            else
                prefixes[i].Str = node.Env.StrManager.Concat(newStr, prefixes[i].Str);
            prefixes[i].SideConstraints.Add(leastZero);
            prefixes[i].SideConstraints.Add(lessThanPower);
        }

        return prefixes;
    }

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