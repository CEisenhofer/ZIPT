using System.Numerics;
using Microsoft.Z3;
using ZIPT.Constraints;
using ZIPT.Strings;
using ZIPT.Strings.Chunks;

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

    public override IntExpr ToExpr(NielsenGraph graph) => 
        (IntExpr)graph.Env.IndexOfFct.Apply(S.ToExpr(graph), Contained.ToExpr(graph), Start.ToExpr(graph));

    public sealed override string ToString() => $"indexOf({S},{Contained},{Start})";
}