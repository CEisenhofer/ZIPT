using Microsoft.Z3;
using ZIPT.Constraints;

namespace ZIPT.Strings.Tokens;

public sealed class StrVarToken : NamedStrToken {
    public override string OriginalName { get; }

    StrVarToken(StrVarToken parent) : base(parent) {
        OriginalName = parent.OriginalName;
    }

    public StrVarToken(string name) {
        Log.Caller(nameof(Environment.GetOrCreateStrVar));
        OriginalName = name;
    }

    public override StrVarToken GetExtension1() => (StrVarToken)(Extension1 ??= new StrVarToken(this));
    public override StrVarToken GetExtension2() => (StrVarToken)(Extension2 ??= new StrVarToken(this));

    public override Expr ToExpr(Environment env, Dictionary<NamedStrToken, int> currentModificationCnt) {
        Expr? e = env.GetCachedStrExpr(this, currentModificationCnt);
        if (e is not null)
            return e;
        FuncDecl f = env.Ctx.MkFreshConstDecl(Name, env.StringSort);
        e = env.Ctx.MkUserPropagatorFuncDecl(f.Name.ToString(), [], env.StringSort).Apply();
        env.SetCachedExpr(this, e, currentModificationCnt);
        return e;
    }

    public Expr ToExpr(Environment env) {
        Expr? e = env.GetCachedStrExpr(this, 0);
        if (e is not null)
            return e;
        FuncDecl f = env.Ctx.MkFreshConstDecl(Name, env.StringSort);
        e = env.Ctx.MkUserPropagatorFuncDecl(f.Name.ToString(), [], env.StringSort).Apply();
        env.SetCachedExpr(this, e, 0);
        return e;
    }
}