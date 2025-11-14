using Microsoft.Z3;
using ZIPT.Constraints;

namespace ZIPT.Strings.Tokens.RegexTokens;
#if false
public class PostToken : NamedStrToken {

    readonly uint id;

    public override string OriginalName => id + ">";
    public override bool RegexFree => false;

    public PostToken(uint id) {
        this.id = id;
    }

    public override Expr ToExpr(Environment env, Dictionary<NamedStrToken, int> currentModificationCnt) {
        Expr? e = env.GetCachedStrExpr(this, info);
        if (e is not null)
            return e;
        FuncDecl f = info.Ctx.MkFreshConstDecl(Name, info.Env.StringSort);
        e = info.Ctx.MkUserPropagatorFuncDecl(f.Name.ToString(), [], info.Env.StringSort).Apply();
        info.Env.SetCachedExpr(this, e, info);
        return e;
    }

    public override NamedStrToken GetExtension1() =>
        throw new NotSupportedException();

    public override NamedStrToken GetExtension2() =>
        throw new NotSupportedException();
}
#endif