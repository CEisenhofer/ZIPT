using System.Diagnostics;
using Microsoft.Z3;
using ZIPT.Constraints;
using ZIPT.Constraints.ConstraintElement;
using ZIPT.Constraints.ConstraintElement.AuxConstraints;
using ZIPT.IntUtils;
using ZIPT.Tokens;
using ZIPT.Tokens.AuxTokens;

namespace ZIPT;

public class ExpressionCache : IDisposable {

    bool disposed;

    public readonly Context Ctx;
    public readonly Sort StringSort;

    public readonly FuncDecl ConcatFct;
    public readonly FuncDecl PowerFct;

    public bool IsConcat(FuncDecl f) => f.Equals(ConcatFct);
    public bool IsPower(FuncDecl f) => f.Equals(PowerFct);

    public readonly FuncDecl LenFct;

    public bool IsLen(FuncDecl f) => f.Equals(LenFct);

    public readonly Expr Epsilon;

    // The easy functions
    public readonly FuncDecl StrAtFct;
    public readonly FuncDecl PrefixOfFct;
    public readonly FuncDecl SuffixOfFct;
    public readonly FuncDecl SubstringFct;

    public bool IsStrAt(FuncDecl f) => f.Equals(StrAtFct);
    public bool IsPrefixOf(FuncDecl f) => f.Equals(PrefixOfFct);
    public bool IsSuffixOf(FuncDecl f) => f.Equals(SuffixOfFct);
    public bool IsSubstring(FuncDecl f) => f.Equals(SubstringFct);

    // The tricky ones
    // contains, indexOf, (replace, replaceAll)
    public readonly FuncDecl ContainsFct;
    public readonly FuncDecl IndexOfFct;

    public bool IsContains(FuncDecl f) => f.Equals(ContainsFct);
    public bool IsIndexOf(FuncDecl f) => f.Equals(IndexOfFct);

    public readonly Dictionary<(StrToken v, int modifications), Expr> StrTokenToExpr = [];
    public readonly Dictionary<Expr, StrToken> ExprToStrToken = [];

    public readonly Dictionary<(NonTermInt v, int modifications), IntExpr> IntTokenToExpr = [];
    public readonly Dictionary<IntExpr, NonTermInt> ExprToIntToken = [];

    public ExpressionCache(Context ctx) {
        Ctx = ctx;
        StringSort = ctx.MkUninterpretedSort("Str");
        Epsilon = ctx.MkUserPropagatorFuncDecl("epsilon", [], StringSort).Apply();
        ConcatFct = ctx.MkUserPropagatorFuncDecl("concat", [StringSort, StringSort], StringSort);
        PowerFct = ctx.MkUserPropagatorFuncDecl("power", [StringSort, ctx.IntSort], StringSort);
        LenFct = ctx.MkUserPropagatorFuncDecl("len", [StringSort], ctx.IntSort);

        StrAtFct = ctx.MkUserPropagatorFuncDecl("strAt", [StringSort], StringSort);
        PrefixOfFct = ctx.MkUserPropagatorFuncDecl("prefixOf", [StringSort, StringSort], ctx.BoolSort);
        SuffixOfFct = ctx.MkUserPropagatorFuncDecl("suffixOf", [StringSort, StringSort], ctx.BoolSort);
        SubstringFct = ctx.MkUserPropagatorFuncDecl("subStr", [StringSort, ctx.IntSort, ctx.IntSort], StringSort);

        ContainsFct = ctx.MkUserPropagatorFuncDecl("contains", [StringSort, StringSort], ctx.BoolSort);
        IndexOfFct = ctx.MkUserPropagatorFuncDecl("indexOf", [StringSort, StringSort, ctx.IntSort], ctx.IntSort);
    }

    public void Dispose() {
        if (disposed)
            return;
        disposed = true;
        StrTokenToExpr.Clear();
        ExprToIntToken.Clear();
        StrVarToken.DisposeAll();
    }

    public int GetModCnt(StrToken t, NielsenGraph graph) =>
        t is not NamedStrToken n || !graph.CurrentModificationCnt.TryGetValue(n, out int mod) ? 0 : mod;

    public Expr? GetCachedStrExpr(StrToken t, NielsenGraph graph) => 
        GetCachedStrExpr(t, t is NamedStrToken n && graph.CurrentModificationCnt.TryGetValue(n, out int mod) ? mod : 0);

    public Expr? GetCachedStrExpr(StrToken t, int mod) => 
        StrTokenToExpr.GetValueOrDefault((t, mod));

    public IntExpr? GetCachedIntExpr(NonTermInt t, NielsenGraph graph) => 
        IntTokenToExpr.GetValueOrDefault((t, t is StrDepIntVar n && graph.CurrentModificationCnt.TryGetValue(n.Var, out int mod) ? mod : 0));

    public void SetCachedExpr(StrToken t, Expr e, NielsenGraph graph) {
        if (t is not NamedStrToken n || !graph.CurrentModificationCnt.TryGetValue(n, out int mod))
            mod = 0;
        SetCachedExpr(t, e, mod);
    }

    public void SetCachedExpr(StrToken t, Expr e, int mod) {
        StrTokenToExpr.Add((t, mod), e);
        ExprToStrToken.Add(e, t);
    }

    public void SetCachedExpr(NonTermInt t, IntExpr e, NielsenGraph graph) {
        if (t is not StrDepIntVar n || !graph.CurrentModificationCnt.TryGetValue(n.Var, out int mod))
            mod = 0;
        IntTokenToExpr.Add((t, mod), e);
        ExprToIntToken.Add((IntExpr)e.Dup(), t);
    }

    public IntExpr MkLen(Expr e) =>
        (IntExpr)LenFct.Apply(e);

    public Expr MkConcat(Expr e1, Expr e2) {
        if (e1.Equals(Epsilon))
            return e2;
        if (e2.Equals(Epsilon))
            return e1;
        return ConcatFct.Apply(e1, e2);
    }

    public Expr MkPower(Expr e, IntExpr n) {
        if (n.Equals(Ctx.MkInt(0)))
            return Epsilon;
        if (n.Equals(Ctx.MkInt(1)))
            return e;
        return PowerFct.Apply(e, n);
    }

    // Translate Z3's string terms to our custom ones such that the UP gets the callbacks
    public Expr? TranslateStr(Expr e, NielsenGraph graph) {
        if (e.IsVar)
            return null;
        if (e.IsString)
            return new Str(e.String.Select(o => (StrToken)new CharToken(o)).ToArray()).ToExpr(graph);

        var f = e.FuncDecl;
        var kind = f.DeclKind;
        switch (kind) {
            case Z3_decl_kind.Z3_OP_SEQ_AT:
                return StrAtFct.Apply(
                    TranslateStr(e.Arg(0), graph) ?? e.Arg(0),
                    TranslateStr(e.Arg(1), graph) ?? e.Arg(1));
            case Z3_decl_kind.Z3_OP_SEQ_CONCAT:
                return ConcatFct.Apply(
                    TranslateStr(e.Arg(0), graph) ?? e.Arg(0),
                    TranslateStr(e.Arg(1), graph) ?? e.Arg(1));
            case Z3_decl_kind.Z3_OP_SEQ_PREFIX:
                return PrefixOfFct.Apply(
                    TranslateStr(e.Arg(0), graph) ?? e.Arg(0),
                    TranslateStr(e.Arg(1), graph) ?? e.Arg(1));
            case Z3_decl_kind.Z3_OP_SEQ_SUFFIX:
                return SuffixOfFct.Apply(
                    TranslateStr(
                        e.Arg(0), graph) ?? e.Arg(0),
                    TranslateStr(e.Arg(1), graph) ?? e.Arg(1));
            case Z3_decl_kind.Z3_OP_SEQ_CONTAINS:
                return ContainsFct.Apply(
                    TranslateStr(e.Arg(0), graph) ?? e.Arg(0),
                    TranslateStr(e.Arg(1), graph) ?? e.Arg(1));
            case Z3_decl_kind.Z3_OP_SEQ_INDEX:
                return IndexOfFct.Apply(
                    TranslateStr(e.Arg(0), graph) ?? e.Arg(0),
                    TranslateStr(e.Arg(1), graph) ?? e.Arg(1),
                    TranslateStr(e.Arg(2), graph) ?? e.Arg(2));
            case Z3_decl_kind.Z3_OP_SEQ_LENGTH:
                return MkLen(TranslateStr(e.Arg(0), graph) ?? e.Arg(0));
            case Z3_decl_kind.Z3_OP_SEQ_EXTRACT:
                return SubstringFct.Apply(
                    TranslateStr(e.Arg(0), graph) ?? e.Arg(0),
                    TranslateStr(e.Arg(1), graph) ?? e.Arg(1),
                    TranslateStr(e.Arg(2), graph) ?? e.Arg(2));
            case Z3_decl_kind.Z3_OP_UNINTERPRETED when e is SeqExpr:
                return StrVarToken.GetOrCreate(f.Name.ToString()).ToExpr(graph);
            case Z3_decl_kind.Z3_OP_EQ when e.Arg(0) is SeqExpr:
                return Ctx.MkEq(
                    TranslateStr(e.Arg(0), graph) ?? e.Arg(0),
                    TranslateStr(e.Arg(1), graph) ?? e.Arg(1));
            default:
                Expr[] args = new Expr[e.NumArgs];
                bool mod = false;
                for (uint i = 0; i < e.NumArgs; i++) {
                    var arg = e.Arg(i);
                    var n = TranslateStr(arg, graph);
                    mod |= n is not null;
                    args[i] = n ?? arg;
                }
                if (kind != Z3_decl_kind.Z3_OP_UNINTERPRETED &&
                    args.Any(o => o.Sort.Equals(StringSort)))
                    throw new NotSupportedException("Function " + f + " currently not supported");
                return mod ? Ctx.MkApp(e.FuncDecl, args) : null;
        }
    }

    public Constraint? TryParse(BoolExpr expr) {
        FuncDecl decl = expr.FuncDecl;
        if (decl.Equals(PrefixOfFct))
            return ParsePrefix(expr.Arg(0), expr.Arg(1));
        if (decl.Equals(SuffixOfFct))
            return ParseSuffix(expr.Arg(0), expr.Arg(1));
        if (decl.Equals(ContainsFct))
            return ParseContains(expr.Arg(0), expr.Arg(1));
        switch (decl.DeclKind) {
            case Z3_decl_kind.Z3_OP_EQ:
                return expr.Arg(0) is IntExpr
                    ? ParseIntEq((IntExpr)expr.Args[0], (IntExpr)expr.Args[1])
                    : ParseStrEq(expr.Args[0], expr.Args[1]);
            case Z3_decl_kind.Z3_OP_NOT:
                return TryParse((BoolExpr)expr.Args[0])?.Negate();
            case Z3_decl_kind.Z3_OP_LE:
                return ParseLe((IntExpr)expr.Args[0], (IntExpr)expr.Args[1]);
            case Z3_decl_kind.Z3_OP_GE:
                return ParseLe((IntExpr)expr.Args[1], (IntExpr)expr.Args[0]);
            case Z3_decl_kind.Z3_OP_LT:
                return ParseLt((IntExpr)expr.Args[0], (IntExpr)expr.Args[1]);
            case Z3_decl_kind.Z3_OP_GT:
                return ParseLe((IntExpr)expr.Args[1], (IntExpr)expr.Args[0]);
            case Z3_decl_kind.Z3_OP_SEQ_PREFIX:
                return ParsePrefix(expr.Args[0], expr.Args[1]);
            case Z3_decl_kind.Z3_OP_SEQ_SUFFIX:
                return ParseSuffix(expr.Args[0], expr.Args[1]);
            case Z3_decl_kind.Z3_OP_SEQ_CONTAINS:
                return ParseContains(expr.Args[0], expr.Args[1]);
            default:
                throw new NotSupportedException(expr.FuncDecl.Name.ToString());
        }
    }

    public StrEq? ParseStrEq(Expr left, Expr right) {
        var lhs = TryParseStr(left);
        if (lhs is null)
            return null;
        var rhs = TryParseStr(right);
        return rhs is null ? null : new StrEq(lhs, rhs);
    }

    public IntEq? ParseIntEq(IntExpr left, IntExpr right) {
        var lhs = TryParseInt(left);
        if (lhs is null)
            return null;
        var rhs = TryParseInt(right);
        return rhs is null ? null : new IntEq(lhs, rhs);
    }

    public IntLe? ParseLe(IntExpr left, IntExpr right) {
        var lhs = TryParseInt(left);
        if (lhs is null)
            return null;
        var rhs = TryParseInt(right);
        return rhs is null ? null : IntLe.MkLe(lhs, rhs);
    }

    public IntLe? ParseLt(IntExpr left, IntExpr right) {
        var lhs = TryParseInt(left);
        if (lhs is null)
            return null;
        var rhs = TryParseInt(right);
        return rhs is null ? null : IntLe.MkLt(lhs, rhs);
    }

    public StrPrefixOf? ParsePrefix(Expr contained, Expr str) {
        var c = TryParseStr(contained);
        if (c is null)
            return null;
        var s = TryParseStr(str);
        return s is null ? null : new StrPrefixOf(c, s, false);
    }

    public StrSuffixOf? ParseSuffix(Expr contained, Expr str) {
        var c = TryParseStr(contained);
        if (c is null)
            return null;
        var s = TryParseStr(str);
        return s is null ? null : new StrSuffixOf(c, s, false);
    }

    public StrContains? ParseContains(Expr str, Expr contained) {
        var s = TryParseStr(str);
        if (s is null)
            return null;
        var c = TryParseStr(contained);
        return c is null ? null : new StrContains(s, c, false);
    }

    public Str? TryParseStr(Expr expr) {
        FuncDecl f = expr.FuncDecl;
        if (expr.Sort.Equals(StringSort)) {
            // Custom Z3
            if (expr.Equals(Epsilon))
                return [];
            if (IsConcat(f)) {
                List<StrToken> res = [];
                for (uint i = 0; i < expr.NumArgs; i++) {
                    if (TryParseStr(expr.Arg(i)) is not { } str)
                        return null;
                    res.AddRange(str);
                }
                return new Str(res);
            }
            if (IsPower(f)) {
                Str? @base = TryParseStr(expr.Arg(0));
                if (@base is null)
                    return null;
                IntPoly? p = TryParseInt((IntExpr)expr.Arg(1));
                if (p is null)
                    return null;
                return new Str([new PowerToken(@base, p)]);
            }
            if (IsStrAt(f)) {
                Str? @base = TryParseStr(expr.Arg(0));
                if (@base is null)
                    return null;
                IntPoly? at = TryParseInt((IntExpr)expr.Arg(1));
                if (at is null)
                    return null;
                return [new StrAtToken(@base, at)];
            }
            if (IsSubstring(f)) {
                Str? @base = TryParseStr(expr.Arg(0));
                if (@base is null)
                    return null;
                IntPoly? from = TryParseInt((IntExpr)expr.Arg(1));
                if (from is null)
                    return null;
                IntPoly? len = TryParseInt((IntExpr)expr.Arg(2));
                if (len is null)
                    return null;
                return [new SubStrToken(@base, from, len)];
            }
            if (ExprToStrToken.TryGetValue(expr, out StrToken? s))
                return [s];
        }
        else if (expr.Sort is SeqSort) {
            // Native Z3
            if (expr.IsString)
                return new Str(expr.String.Select(o => (StrToken)new CharToken(o)).ToArray());
            if (expr.IsConst)
                return new Str([StrVarToken.GetOrCreate(f.Name.ToString())]);
            if (expr.IsConcat) {
                Str r = [];
                foreach (var arg in expr.Args) {
                    Str? q = TryParseStr(arg);
                    if (q is null)
                        return null;
                    r.AddLastRange(q);
                }
                return r;
            }
            if (expr.IsAt) {
                Str? s = TryParseStr(expr.Args[0]);
                if (s is null)
                    return null;
                IntPoly? p = TryParseInt((IntExpr)expr.Args[1]);
                if (p is null)
                    return null;
                return [new StrAtToken(s, p)];
            }
            if (expr.IsExtract) {
                Str? @base = TryParseStr(expr.Arg(0));
                if (@base is null)
                    return null;
                IntPoly? from = TryParseInt((IntExpr)expr.Arg(1));
                if (from is null)
                    return null;
                IntPoly? len = TryParseInt((IntExpr)expr.Arg(2));
                if (len is null)
                    return null;
                return [new SubStrToken(@base, from, len)];
            }
        }
        throw new NotSupportedException(f.Name.ToString());
    }

    public IntPoly? TryParseInt(IntExpr expr) {
        if (expr.Sort is not IntSort)
            return null;
        if (expr is IntNum num)
            return new IntPoly(num.BigInteger);
        if (expr.FuncDecl.Equals(LenFct) || expr.IsLength) {
            Str? str = TryParseStr(expr.Arg(0));
            return str is null ? null : LenVar.MkLenPoly(str);
        }
        if (expr.FuncDecl.Equals(IndexOfFct) || expr.IsIndex) {
            if (expr.NumArgs != 3)
                return null;
            Str? str = TryParseStr(expr.Arg(0));
            if (str is null)
                return null;
            Str? contained = TryParseStr(expr.Arg(1));
            if (contained is null)
                return null;
            IntPoly? start = TryParseInt((IntExpr)expr.Arg(2));
            return start is null ? null : new IntPoly(new IndexOfVar(str, contained, start));
        }
        if (ExprToIntToken.TryGetValue(expr, out var v))
            return new IntPoly(v);
        if (expr.IsAdd) {
            var polys = new IntPoly[expr.NumArgs];
            for (uint i = 0; i < expr.NumArgs; i++) {
                IntPoly? p = TryParseInt((IntExpr)expr.Arg(i));
                if (p is null)
                    return null;
                polys[i] = p;
            }
            if (polys.Length == 0)
                return new IntPoly();
            IntPoly poly = polys[0];
            for (int i = 1; i < polys.Length; i++) {
                poly.Plus(polys[i]);
            }
            return poly;
        }
        if (expr.IsSub) {
            // What if we have more than two arguments?
            Debug.Assert(expr.NumArgs <= 2);
            var polys = new IntPoly[expr.NumArgs];
            for (uint i = 0; i < expr.NumArgs; i++) {
                IntPoly? p = TryParseInt((IntExpr)expr.Arg(i));
                if (p is null)
                    return null;
                polys[i] = p;
            }
            if (polys.Length == 0)
                return new IntPoly();
            IntPoly poly = polys[0];
            for (int i = 1; i < polys.Length; i++) {
                poly.Sub(polys[i]);
            }
            return poly;
        }
        if (expr.IsMul) {
            var polys = new IntPoly[expr.NumArgs];
            for (uint i = 0; i < expr.NumArgs; i++) {
                IntPoly? p = TryParseInt((IntExpr)expr.Arg(i));
                if (p is null)
                    return null;
                polys[i] = p;
            }
            if (polys.Length == 0)
                return new IntPoly(1);
            IntPoly poly = polys[0];
            for (int i = 1; i < polys.Length; i++) {
                poly = IntPoly.Mul(poly, polys[i]);
            }
            return poly;
        }
        throw new NotSupportedException(expr.FuncDecl.Name.ToString());
    }

}