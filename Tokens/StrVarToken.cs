using System.Diagnostics;
using Microsoft.Z3;
using StringBreaker.Constraints;
using StringBreaker.Constraints.ConstraintElement;
using StringBreaker.IntUtils;

namespace StringBreaker.Tokens;

public sealed class StrVarToken : StrToken, IDisposable {
    public override bool Ground => false;

    static readonly Dictionary<string, StrVarToken> Cache = [];

    public string OriginalName { get; }
    public string Name => Aux ? $"{OriginalName}${ChildIdx}" : OriginalName;
    public bool Aux => ChildIdx != 0;
    public int ChildIdx { get; }
    public StrVarToken? Parent { get; }
    StrVarToken? PostExtension { get; set; }
    IntVar? PowerExtension { get; set; }

    StrVarToken(StrVarToken parent) {
        OriginalName = parent.OriginalName;
        Parent = parent;
        ChildIdx = parent.ChildIdx + 1;
        Debug.Assert(ChildIdx > 0);
        Debug.Assert(Cache.ContainsKey(OriginalName));
    }

    StrVarToken(string name) {
        Cache.Add(name, this);
        OriginalName = name;
        ChildIdx = 0;
        Parent = null;
    }

    public void Dispose() {
        PowerExtension = null;
        PostExtension = null;
        if (!Aux)
            Cache.Remove(OriginalName);
    }

    public static void DisposeAll() {
        foreach (var v in Cache) {
            v.Value.Dispose();
        }
        Cache.Clear();
    }

    public StrVarToken GetPostExtension() => 
        PostExtension ??= new StrVarToken(this);

    public IntVar GetPowerExtension() => 
        PowerExtension ??= new IntVar();

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

    public static StrVarToken CreateFreshAux(string name) =>
        new(GetNextFreshName(name));

    public override bool IsNullable(NielsenNode node) => 
        LenVar.MkLenPoly([this]).GetBounds(node).Contains(0);

    public override Str Apply(Subst subst) => subst.ResolveVar(this);
    public override Str Apply(Interpretation subst) => subst.ResolveVar(this);

    public override List<(Str str, List<IntConstraint> sideConstraints, Subst? varDecomp)> GetPrefixes() {
        // P(x) := y with x = yz, |y| < |x|
        // TODO
        StrVarToken y = CreateFreshAux(Name);
        StrVarToken z = CreateFreshAux(Name);
        Poly yl = new(LenVar.MkLenPoly([y]));
        Poly xl = new(LenVar.MkLenPoly([this]));
        yl.AddPoly(new Poly(1));
        return [([y], [new IntLe(yl, xl)], new Subst(this, [y, z]))];
    }

    public override Expr ToExpr(NielsenGraph graph) {
        Expr? e = graph.Propagator.GetCachedStrExpr(this);
        if (e is not null)
            return e;
        e = graph.Ctx.MkFreshConst(Name, graph.Propagator.StringSort);
        e = graph.Ctx.MkUserPropagatorFuncDecl(e.FuncDecl.Name.ToString(), [], graph.Propagator.StringSort).Apply();
        graph.Propagator.SetCachedExpr(this, e);
        return e;
    }

    public override bool RecursiveIn(StrVarToken v) => Equals(v);

    protected override int CompareToInternal(StrToken other) {
        Debug.Assert(other is StrVarToken);
        return string.Compare(Name, ((StrVarToken)other).Name, StringComparison.Ordinal);
    }

    public override bool Equals(StrToken? other) =>
        other is StrVarToken token && Equals(token);

    public bool Equals(StrVarToken other) =>
        CompareToInternal(other) == 0;

    public override int GetHashCode() => 509077363 * Name.GetHashCode();

    public override string ToString(NielsenGraph? graph) => Name;
}