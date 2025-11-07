using Microsoft.Z3;
using ZIPT.Constraints;

namespace ZIPT.Strings.Tokens.RegexTokens;

public class PreToken : NamedStrToken {

    readonly uint id;

    public override string OriginalName => "<" + id;
    public override bool RegexFree => false;

    public PreToken(uint id) {
        this.id = id;
    }

    public override Expr ToExpr(NielsenGraph graph) {
        Expr? e = graph.Env.GetCachedStrExpr(this, graph);
        if (e is not null)
            return e;
        FuncDecl f = graph.Env.Ctx.MkFreshConstDecl(Name, graph.Env.StringSort);
        e = graph.Env.Ctx.MkUserPropagatorFuncDecl(f.Name.ToString(), [], graph.Env.StringSort).Apply();
        graph.Env.SetCachedExpr(this, e, graph);
        return e;
    }

    public override NamedStrToken GetExtension1() => 
        throw new NotSupportedException();

    public override NamedStrToken GetExtension2() =>
        throw new NotSupportedException();
}