using System.Diagnostics;
using System.Runtime.Intrinsics.X86;
using Microsoft.Z3;
using ZIPT.MiscUtils;
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

    public override Expr ToExpr(NielsenGraph graph) {
        Expr? e = graph.Env.GetCachedStrExpr(this, graph);
        if (e is not null)
            return e;
        FuncDecl f = graph.Env.Ctx.MkFreshConstDecl(Name, graph.Env.StringSort);
        e = graph.Env.Ctx.MkUserPropagatorFuncDecl(f.Name.ToString(), [], graph.Env.StringSort).Apply();
        graph.Env.SetCachedExpr(this, e, graph);
        return e;
    }
}