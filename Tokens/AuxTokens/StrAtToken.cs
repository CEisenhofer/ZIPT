using Microsoft.Z3;
using StringBreaker.Constraints;
using StringBreaker.IntUtils;

namespace StringBreaker.Tokens.AuxTokens;

public sealed class StrAtToken : NamedStrToken {

    public Str S { get; }
    public Poly I { get; }

    public override string OriginalName => $"strAt({S},{I})";

    public StrAtToken(Str s, Poly i) {
        S = s;
        I = i;
    }

    public override StrAtToken GetExtension1() => (StrAtToken)(Extension1 ??= new StrAtToken(S, I));
    public override StrAtToken GetExtension2() => (StrAtToken)(Extension2 ??= new StrAtToken(S, I));

    public override Expr ToExpr(NielsenGraph graph) {
        Expr? e = graph.Cache.GetCachedStrExpr(this, graph);
        if (e is not null)
            return e;
        e = graph.Cache.StrAtFct.Apply(S.ToExpr(graph), I.ToExpr(graph));
        graph.Cache.SetCachedExpr(this, e, graph);
        return e;
    }
}