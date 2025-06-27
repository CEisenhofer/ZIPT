using Microsoft.Z3;
using ZIPT.Constraints;

namespace ZIPT.IntUtils;

public class IndexOfVar : IntVar {

    public Str S { get; }
    public Str Contained { get; }
    public IntPoly Start { get; }

    public override BigIntInf MinLen => -1;

    public IndexOfVar(Str s, Str contained, IntPoly start) {
        S = s;
        Contained = contained;
        Start = start;
    }

    public override IntExpr ToExpr(NielsenGraph graph) => 
        (IntExpr)graph.Cache.IndexOfFct.Apply(S.ToExpr(graph), Contained.ToExpr(graph), Start.ToExpr(graph));

    public sealed override string ToString() => $"indexOf({S},{Contained},{Start})";
}