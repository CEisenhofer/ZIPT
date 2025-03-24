using System.Diagnostics;
using Microsoft.Z3;
using StringBreaker.Constraints;

namespace StringBreaker.Tokens;

public sealed class StrVarToken : NamedStrToken, IDisposable {

    static readonly Dictionary<string, StrVarToken> Cache = [];

    public override string OriginalName { get; }

    StrVarToken(StrVarToken parent) : base(parent) {
        OriginalName = parent.OriginalName;
        Debug.Assert(Cache.ContainsKey(OriginalName));
    }

    StrVarToken(string name) {
        Cache.Add(name, this);
        OriginalName = name;
    }

    public void Dispose() {
        if (!Aux)
            Cache.Remove(OriginalName);
    }

    public static void DisposeAll() {
        foreach (var v in Cache) {
            v.Value.Dispose();
        }
        Cache.Clear();
    }

    public override StrVarToken GetExtension1() => (StrVarToken)(Extension1 ??= new StrVarToken(this));
    public override StrVarToken GetExtension2() => (StrVarToken)(Extension2 ??= new StrVarToken(this));

    public static StrVarToken GetOrCreate(string var) {
        if (Cache.TryGetValue(var, out StrVarToken? v))
            return v;
        Debug.Assert(!var.Contains('$'));
        Debug.Assert(!var.Contains('#'));
        v = new StrVarToken(var);
        return v;
    }

    public static string GetFreshName(string name, int start = 1) {
        for (; start < int.MaxValue; start++) {
            if (!Cache.ContainsKey($"{name}#{start}"))
                return $"{name}#{start}";
        }
        Debug.Assert(false);
        return "";
    }

    public static string GetNextFreshName(string name) {
        int idx = name.LastIndexOf('#');
        if (idx == -1)
            return GetFreshName(name);
        return int.TryParse(name[(idx + 1)..], out int num)
            ? GetFreshName(name[..idx], num + 1)
            : GetFreshName(name);
    }

    public override Expr ToExpr(NielsenGraph graph) {
        Expr? e = graph.Propagator.GetCachedStrExpr(this);
        if (e is not null)
            return e;

        FuncDecl f = graph.Ctx.MkFreshConstDecl(Name, graph.Propagator.StringSort);
        e = graph.Ctx.MkUserPropagatorFuncDecl(f.Name.ToString(), [], graph.Propagator.StringSort).Apply();
        graph.Propagator.SetCachedExpr(this, e);
        return e;
    }
}