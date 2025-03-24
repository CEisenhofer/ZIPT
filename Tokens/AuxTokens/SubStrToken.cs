using Microsoft.Z3;
using StringBreaker.Constraints;
using StringBreaker.IntUtils;

namespace StringBreaker.Tokens.AuxTokens;

public sealed class SubStrToken : NamedStrToken {

    public Str S { get; }
    public Poly From { get; }
    public Poly Len { get; }

    public override string OriginalName => $"subStr({S},{From},{Len})";

    public SubStrToken(Str s, Poly from, Poly len) {
        S = s;
        From = from;
        Len = len;
    }

    public override SubStrToken GetExtension1() => (SubStrToken)(Extension1 ??= new SubStrToken(S, From, Len));
    public override SubStrToken GetExtension2() => (SubStrToken)(Extension2 ??= new SubStrToken(S, From, Len));

    public override Expr ToExpr(NielsenGraph graph) {
        Expr? e = graph.Propagator.GetCachedStrExpr(this);
        if (e is not null)
            return e;
        e = graph.Propagator.StrAtFct.Apply(S.ToExpr(graph), From.ToExpr(graph), Len.ToExpr(graph));
        graph.Propagator.SetCachedExpr(this, e);
        return e;
    }
}