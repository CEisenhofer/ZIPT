using Microsoft.Z3;
using ZIPT.Constraints;
using ZIPT.IntUtils;

namespace ZIPT.Tokens.AuxTokens;

public sealed class SubStrToken : NamedStrToken {

    public IStr S { get; }
    public IntPoly From { get; }
    public IntPoly Len { get; }

    public override string OriginalName => $"subStr({S},{From},{Len})";

    public SubStrToken(IStr s, IntPoly from, IntPoly len) {
        S = s;
        From = from;
        Len = len;
    }

    public override SubStrToken GetExtension1() => (SubStrToken)(Extension1 ??= new SubStrToken(S, From, Len));
    public override SubStrToken GetExtension2() => (SubStrToken)(Extension2 ??= new SubStrToken(S, From, Len));

    public override Expr ToExpr(NielsenGraph graph) {
        Expr? e = graph.Env.GetCachedStrExpr(this, graph);
        if (e is not null)
            return e;
        e = graph.Env.StrAtFct.Apply(S.ToExpr(graph), From.ToExpr(graph), Len.ToExpr(graph));
        graph.Env.SetCachedExpr(this, e, graph);
        return e;
    }
}