using Microsoft.Z3;
using StringBreaker.Constraints;
using StringBreaker.IntUtils;
using StringBreaker.Strings.Tokens;

namespace StringBreaker.Strings.Tokens.AuxTokens;

public sealed class SubStrToken : NamedStrToken {

    public StrRef S { get; }
    public Poly From { get; }
    public Poly Len { get; }

    public override string OriginalName => $"subStr({S},{From},{Len})";

    public SubStrToken(StrRef s, Poly from, Poly len) {
        S = s;
        From = from;
        Len = len;
    }

    public override SubStrToken GetExtension1() => (SubStrToken)(Extension1 ??= new SubStrToken(S, From, Len));
    public override SubStrToken GetExtension2() => (SubStrToken)(Extension2 ??= new SubStrToken(S, From, Len));

    public override Expr ToExpr(int copyIdx, NielsenContext ctx) {
        Expr? e = ctx.Cache.GetCachedStrExpr(this, copyIdx);
        if (e is not null)
            return e;
        e = ctx.Cache.StrAtFct.Apply(S.ToExpr(ctx), From.ToExpr(ctx), Len.ToExpr(ctx));
        ctx.Cache.SetCachedExpr(this, e, copyIdx);
        return e;
    }
}