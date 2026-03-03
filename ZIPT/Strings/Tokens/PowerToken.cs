using System.Diagnostics;
using System.Numerics;
using Microsoft.Z3;
using ZIPT.Constraints;
using ZIPT.Constraints.ConstraintElement;
using ZIPT.IntUtils;
using ZIPT.MiscUtils;
using ZIPT.Strings.Chunks;

namespace ZIPT.Strings.Tokens;

// Token representing a repeated substring `Base^{Power}`; used for compact loops and arithmetic-powered repetition.
// Token representing repeated substring `Base^{Power}`. Used to compactly encode repetitions
// and to support power-aware splitting and unwinding during search.
public sealed class PowerToken : StrToken {

    public Str Base { get; }
    public PDD<BigInteger> Power { get; }

    public override bool Ground => Base.Ground;
    public override bool RegexFree => Base.RegexFree;
    public override bool Derivable => false;
    public override bool Nullable => Base.Nullable;
    public override bool BasicRegex => true;
    // !(0 < Power) && Base is nullable
    // !node.IsLt(node.Env.ZeroInt, Power) && Base.IsNullable(node);

    public PowerToken(Str b, PDD<BigInteger> power) {
        Debug.Assert(power.IsLinear);
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

    // Decompose a power token into a bounded repetition `u^m P(u)` for splitting/unwinding.
    public override List<StrDecomposition> GetDecomposition(NielsenNode node, bool fwd) {
        // P(u^n) := u^m P(u) with 0 <= m < n
        IntVar m = new();
        var newExponent = node.Env.IntPDDManager.MkPDD(m);
        PowerToken newPowerToken = new PowerToken(Base, newExponent);
        Str newStr = node.Env.MkString(newPowerToken);
        IntLe leastZero = new IntLe(node.Env.ZeroInt, newExponent, new DependencyTracker(0));
        IntLe lessThanPower = IntLe.MkLt(newExponent, Power, new DependencyTracker(0));

        var decompositions = StrManager.GetDecompose(node, Base, fwd);

        for (int i = 0; i < decompositions.Count; i++) {
            decompositions[i].Prefix = node.Env.StrManager.Concat(newStr, decompositions[i].Prefix, fwd);
            decompositions[i].SideConstraints.Add(leastZero);
            decompositions[i].SideConstraints.Add(lessThanPower);
            // the postfix does not need changes
        }

        return decompositions;
    }

    // Convert power token to an SMT-level representation using the environment's power constructor.
    public override Expr ToExpr(Environment env, Dictionary<NamedStrToken, int> currentModificationCnt) =>
        env.MkPower(Base.ToExpr(env, currentModificationCnt), Power.ToExpr(env, currentModificationCnt));

    protected override int CompareToInternal(StrToken other) {
        int cmp = Base.CompareTo(((PowerToken)other).Base);
        return cmp != 0 ? cmp : Power.CompareTo(((PowerToken)other).Power);
    }

    public override void CollectSymbols(NonTermSet nonTermSet, CharacterSet alphabet) {
        Base.CollectSymbols(nonTermSet, alphabet);
        Power.CollectSymbols(nonTermSet, alphabet);
    }

    public override MinTerms FirstMinTerms() => Base.FirstMinTerms();

    public override MinTerms LastMinTerms() => Base.LastMinTerms();

    public override bool Equals(StrToken? other) =>
        other is PowerToken token && Equals(token);

    public bool Equals(PowerToken other) =>
        Base.Equals(other.Base) && Power.Equals(other.Power);

    public override int GetHashCode() => 495035077 * Base.GetHashCode() + 273877411 * Power.GetHashCode();

    public override Str OptSimplify(StrManager manager) {
        if (Base.IsEmpty())
            return Base;
        if (Power.TryGetConst(out BigInteger val) && val <= Options.ModelUnwindingBound) {
            Str rep = manager.Repeat(Base, (uint)val);
            return rep;
        }
        return manager.Single(this);
    }

    public override string ToString(NielsenGraph? graph) {
        string b = Base.ToString(graph);
        return b.Length == 1 ? $"{b}^{{{Power}}}" : $"({b})^{{{Power}}}";
    }
}