using System.Numerics;
using Microsoft.Z3;
using ZIPT.Strings.Chunks;
using ZIPT.Strings.Tokens;

namespace ZIPT.IntUtils;

public class IndexOfVar : IntVar {

    public Str S { get; }
    public Str Contained { get; }
    public PDD<BigInteger> Start { get; }

    public override InfNum<BigInteger> MinLen => InfNum<BigInteger>.MinusOne;

    public IndexOfVar(Str s, Str contained, PDD<BigInteger> start) {
        S = s;
        Contained = contained;
        Start = start;
    }

    public override IntExpr ToExpr(Environment env, Dictionary<NamedStrToken, int> currentModificationCnt) => 
        (IntExpr)env.IndexOfFct.Apply(S.ToExpr(env, currentModificationCnt), Contained.ToExpr(env, currentModificationCnt), Start.ToExpr(env, currentModificationCnt));

    public sealed override string ToString() => $"indexOf({S},{Contained},{Start})";
}