using System.Diagnostics.Contracts;
using System.Numerics;
using Microsoft.Z3;
using ZIPT.Constraints;
using ZIPT.Strings;
using ZIPT.Strings.Chunks;
using ZIPT.Strings.Tokens;

namespace ZIPT.IntUtils;

public sealed class LenVar : StrDepIntVar {

    public LenVar(NamedStrToken v) : base(v) {}

    public override bool Equals(object? obj) => obj is LenVar var && Equals(var);
    public bool Equals(LenVar other) => Var.Equals(other.Var);

    public override int GetHashCode() => Var.GetHashCode() * 416749777;

    public static PDD<BigInteger> AddLenPoly(StrToken t, PDD<BigInteger> poly, Environment env, Dictionary<NamedInt, PDD<BigInteger>> definitions) {
        switch (t) {
            case UnitToken:
                poly = poly.Add(env.IntPDDManager.One);
                break;
            case NamedStrToken v:
                poly = poly.Add(env.IntPDDManager.MkPDD(new LenVar(v)));
                break;
            case PowerToken pt: {
                var subPoly = MkLenPoly(pt.Base, env, definitions);
                poly = poly.Add(PDD<BigInteger>.MulByDefinitions(subPoly, pt.Power, definitions));
                break;
            }
            default:
                throw new NotSupportedException();
        }
        return poly;
    }

    public static PDD<BigInteger> AddLenPoly(StrToken t, PDD<BigInteger> poly, Environment env) {
        switch (t) {
            case UnitToken:
                poly = poly.Add(env.IntPDDManager.One);
                break;
            case NamedStrToken v:
                poly = poly.Add(env.IntPDDManager.MkPDD(new LenVar(v)));
                break;
            case PowerToken pt: {
                var subPoly = MkLenPoly(pt.Base, env);
                poly = poly.Add(PDD<BigInteger>.Mul(subPoly, pt.Power));
                break;
            }
            default:
                throw new NotSupportedException();
        }
        return poly;
    }

    [Pure]
    public static PDD<BigInteger> MkLenPoly(NamedStrToken s, Environment env) => 
        env.IntPDDManager.MkPDD(new LenVar(s));

    [Pure]
    public static PDD<BigInteger> MkLenPoly(IReadOnlyList<StrToken> s, Environment env) {
        PDD<BigInteger> poly = env.IntPDDManager.Zero;
        foreach (var t in s) {
            poly = AddLenPoly(t, poly, env);
        }
        return poly;
    }

    [Pure]
    public static PDD<BigInteger> MkLenPoly(IReadOnlyList<StrToken> s, Environment env, Dictionary<NamedInt, PDD<BigInteger>> definitions) {
        PDD<BigInteger> poly = env.IntPDDManager.Zero;
        foreach (var t in s) {
            poly = AddLenPoly(t, poly, env, definitions);
        }
        return poly;
    }

    [Pure]
    public static PDD<BigInteger> MkLenPoly(Str s, Environment env, Dictionary<NamedInt, PDD<BigInteger>> definitions) {
        var poly = env.IntPDDManager.Zero;
        foreach (var t in s.GetEnumerator()) {
            poly = AddLenPoly(t, poly, env, definitions);
        }
        return poly;
    }

    [Pure]
    public static PDD<BigInteger> MkLenPoly(Str s, Environment env) {
        var poly = env.IntPDDManager.Zero;
        foreach (var t in s.GetEnumerator()) {
            poly = AddLenPoly(t, poly, env);
        }
        return poly;
    }

    public override int CompareToInternal(NamedInt other) =>
        Var.CompareTo(((LenVar)other).Var);

    public override void CollectSymbols(NonTermSet nonTermSet, HashSet<CharToken> alphabet) => nonTermSet.Add(Var);

    public override IntExpr ToExpr(NielsenGraph graph) {
        IntExpr? e = graph.Env.GetCachedIntExpr(this, graph);
        if (e is not null)
            return e;

        e = (IntExpr)graph.Ctx.MkFreshConst("len_" + Var, graph.Ctx.IntSort);
        graph.Env.SetCachedExpr(this, e, graph);
        return e;
    }

    public override string ToString() => $"|{Var}|";
}