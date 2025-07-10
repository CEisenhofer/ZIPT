using Microsoft.Z3;
using ZIPT.Constraints;

namespace ZIPT.IntUtils;

public class IndexOfVar : IntVar {

    public IStr S { get; }
    public IStr Contained { get; }
    public IntPoly Start { get; }

    public override BigIntInf MinLen => -1;

    public IndexOfVar(IStr s, IStr contained, IntPoly start) {
        S = s;
        Contained = contained;
        Start = start;
    }

    public override IntExpr ToExpr(NielsenGraph graph) => 
        (IntExpr)graph.Env.IndexOfFct.Apply(S.ToExpr(graph), Contained.ToExpr(graph), Start.ToExpr(graph));

    public sealed override string ToString() => $"indexOf({S},{Contained},{Start})";
}