using Microsoft.Z3;

namespace ZIPT.Strings.Tokens.RegexTokens;

#if false
public class PreToken : NamedStrToken {

    readonly uint id;

    public override string OriginalName => "<" + id;
    public override bool RegexFree => false;

    public PreToken(uint id) {
        this.id = id;
    }

    public override Expr ToExpr(Environment env, Dictionary<NamedStrToken, int> currentModificationCnt) {
        Expr? e = env.GetCachedStrExpr(this, currentModificationCnt);
        if (e is not null)
            return e;
        FuncDecl f = env.Ctx.MkFreshConstDecl(Name, env.StringSort);
        e = env.Ctx.MkUserPropagatorFuncDecl(f.Name.ToString(), [], env.StringSort).Apply();
        env.SetCachedExpr(this, e, currentModificationCnt);
        return e;
    }

    public override NamedStrToken GetExtension1() => 
        throw new NotSupportedException();

    public override NamedStrToken GetExtension2() =>
        throw new NotSupportedException();
}
#endif