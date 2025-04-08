using Microsoft.Z3;
using StringBreaker.Constraints;
using StringBreaker.IntUtils;
using StringBreaker.Strings.Tokens;

namespace StringBreaker.Strings.Tokens.AuxTokens;

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

    public override Expr ToExpr(int copyIdx, NielsenContext ctx) {
        Expr? e = ctx.Cache.GetCachedStrExpr(this, copyIdx);
        if (e is not null)
            return e;
        e = ctx.Cache.StrAtFct.Apply(S.ToExpr(ctx), I.ToExpr(ctx));
        ctx.Cache.SetCachedExpr(this, e, copyIdx);
        return e;
    }
}