using Microsoft.Z3;
using System.Diagnostics.Contracts;
using System.Numerics;
using ZIPT.IntUtils;
using ZIPT.Strings.Chunks;
using ZIPT.Strings.Tokens;

namespace ZIPT.Constraints;

public struct Subst {

    public NamedStrToken Var { get; }
    public Str Str { get; }
    public bool IsEliminating => 
        !Str.ContainsVar(Var);

    readonly LenVar lenVar;
    PDD<BigInteger>? newLen;

    public Subst(NamedStrToken v, Str s) {
        Var = v;
        Str = s;
        lenVar = new LenVar(Var);
    }

    [Pure]
    public (LenVar lenVar, PDD<BigInteger> newLen) GetLenReplacement(Environment env) {
        newLen ??= LenVar.MkLenPoly(Str, env);
        return (lenVar, newLen);
    }

    public void AddToInterpretation(Interpretation itp) => itp.Apply(this);
    public IntExpr KeyLenExpr(NielsenGraph graph) => lenVar.ToExpr(graph);
    public IntExpr ValueLenExpr(NielsenGraph graph) =>
        GetLenReplacement(graph.Env).newLen.ToExpr(graph);
    public void CollectValueSymbols(NonTermSet nonTermSet) => Str.CollectSymbols(nonTermSet, []);

    public override string ToString() => $"{Var} / {(Str.Length == 0 ? "ε" : Str)}";

    public override bool Equals(object? obj) =>
        obj is Subst substitution && Equals(substitution);

    public bool Equals(Subst subst) => Var.Equals(subst.Var) && Str.Equals(subst.Str);
    public override int GetHashCode() => HashCode.Combine(Var, Str);
}