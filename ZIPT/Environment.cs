using Microsoft.Z3;
using System.Diagnostics;
using System.Numerics;
using System.Runtime.InteropServices;
using ZIPT.Constraints;
using ZIPT.Constraints.ConstraintElement;
using ZIPT.Constraints.ConstraintElement.AuxConstraints;
using ZIPT.IntUtils;
using ZIPT.Strings;
using ZIPT.Strings.Chunks;
using ZIPT.Strings.Tokens;
using ZIPT.Strings.Tokens.AuxTokens;

namespace ZIPT;

public class Environment : IDisposable {

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

    public readonly Dictionary<(NamedInt v, int modifications), IntExpr> IntTokenToExpr = [];
    public readonly Dictionary<IntExpr, NamedInt> ExprToIntToken = [];

    public EmptyStr EmptyStr => StrManager.EmptyStr;
    public Trie TrieRoot { get; } = new(); // for caching strings (still, strings are unfortunately not canonicalized)
    readonly Dictionary<string, StrVarToken> strVarCache = [];

    public readonly StrManager StrManager;
    public readonly PDD<BigInteger>.PDDManager IntPDDManager = new();
    public readonly PDD<BigRational>.PDDManager RatPDDManager = new();

    public PDD<BigInteger> ZeroInt => IntPDDManager.Zero;
    public PDD<BigInteger> OneInt => IntPDDManager.One;
    public PDD<BigRational> ZeroRat => RatPDDManager.Zero;
    public PDD<BigRational> OneRat => RatPDDManager.One;

    public class Trie {
        public Dictionary<StrToken, Trie> CharChild { get; } = [];
        public Str? Chunk { get; set; }
    }

    public Environment(Context ctx) : this(ctx, new StrManager()) { }

    public Environment(Context ctx, StrManager strManager) {
        Ctx = ctx;
        StrManager = strManager;

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
        strVarCache.Clear();
        StrTokenToExpr.Clear();
        ExprToIntToken.Clear();
    }

    public StrVarToken GetOrCreateStrVar(string var) {
        if (strVarCache.TryGetValue(var, out StrVarToken? v))
            return v;
        Debug.Assert(!var.Contains('$'));
        Debug.Assert(!var.Contains('#'));
        v = new StrVarToken(var);
        strVarCache.Add(var, v);
        return v;
    }

    public string GetFreshName(string name, int start = 1) {
        for (; start < int.MaxValue; start++) {
            if (!strVarCache.ContainsKey($"{name}#{start}"))
                return $"{name}#{start}";
        }
        Debug.Assert(false);
        return "";
    }

    public string GetNextFreshName(string name) {
        int idx = name.LastIndexOf('#');
        if (idx == -1)
            return GetFreshName(name);
        return int.TryParse(name[(idx + 1)..], out int num)
            ? GetFreshName(name[..idx], num + 1)
            : GetFreshName(name);
    }

    public Str MkString(ReadOnlySpan<StrToken> t, bool forward = true) {
        Trie trie = TrieRoot;
        if (forward) {
            for (int i = 0; i < t.Length; i++) {
                if (!trie.CharChild.TryGetValue(t[i], out var child))
                    trie.CharChild[t[i]] = child = new Trie();
                trie = child;
            }
        }
        else {
            for (int i = t.Length; i > 0; i--) {
                if (!trie.CharChild.TryGetValue(t[i - 1], out var child))
                    trie.CharChild[t[i - 1]] = child = new Trie();
                trie = child;
            }
        }
        if (trie.Chunk is null)
            trie.Chunk = StrManager.FromList(t, forward);
        return trie.Chunk;
    }
    public Str MkString(params StrToken[] t) =>
        MkString(t.AsSpan());

    public Str MkString(List<StrToken> tokens, bool forward = true) =>
        MkString(CollectionsMarshal.AsSpan(tokens), forward);

    public Expr? GetCachedStrExpr(StrToken t, NielsenGraph graph) => 
        GetCachedStrExpr(t, t is NamedStrToken n && graph.CurrentModificationCnt.TryGetValue(n, out int mod) ? mod : 0);

    public Expr? GetCachedStrExpr(StrToken t, int mod) => 
        StrTokenToExpr.GetValueOrDefault((t, mod));

    public IntExpr? GetCachedIntExpr(NamedInt t, NielsenGraph graph) => 
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

    public void SetCachedExpr(NamedInt t, IntExpr e, NielsenGraph graph) {
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
            return StrManager.ToExpr(MkString(e.String.Select(o => (StrToken)new CharToken(o)).ToArray()), graph);

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
                return GetOrCreateStrVar(f.Name.ToString()).ToExpr(graph);
            case Z3_decl_kind.Z3_OP_EQ when e.Arg(0) is SeqExpr:
                return Ctx.MkEq(
                    TranslateStr(e.Arg(0), graph) ?? e.Arg(0),
                    TranslateStr(e.Arg(1), graph) ?? e.Arg(1));
            default:
                var args = new Expr[e.NumArgs];
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
        return decl.DeclKind switch {
            Z3_decl_kind.Z3_OP_EQ => expr.Arg(0) is IntExpr
                ? ParseIntEq((IntExpr)expr.Args[0], (IntExpr)expr.Args[1])
                : ParseStrEq(expr.Args[0], expr.Args[1]),
            Z3_decl_kind.Z3_OP_NOT => TryParse((BoolExpr)expr.Args[0])?.Negate(),
            Z3_decl_kind.Z3_OP_LE => ParseLe((IntExpr)expr.Args[0], (IntExpr)expr.Args[1]),
            Z3_decl_kind.Z3_OP_GE => ParseLe((IntExpr)expr.Args[1], (IntExpr)expr.Args[0]),
            Z3_decl_kind.Z3_OP_LT => ParseLt((IntExpr)expr.Args[0], (IntExpr)expr.Args[1]),
            Z3_decl_kind.Z3_OP_GT => ParseLe((IntExpr)expr.Args[1], (IntExpr)expr.Args[0]),
            Z3_decl_kind.Z3_OP_SEQ_PREFIX => ParsePrefix(expr.Args[0], expr.Args[1]),
            Z3_decl_kind.Z3_OP_SEQ_SUFFIX => ParseSuffix(expr.Args[0], expr.Args[1]),
            Z3_decl_kind.Z3_OP_SEQ_CONTAINS => ParseContains(expr.Args[0], expr.Args[1]),
            _ => throw new NotSupportedException(expr.FuncDecl.Name.ToString())
        };
    }

    public StrEq? ParseStrEq(Expr left, Expr right) {
        var lhs = TryParseStr(left);
        if (lhs is null)
            return null;
        var rhs = TryParseStr(right);
        return rhs is null ? null : new StrEq(MkString(lhs), MkString(rhs));
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
        if (s is null)
            return null;
        var ss = MkString(s);
        var sc = MkString(c);
        return new StrPrefixOf(sc, ss, false);
    }

    public StrSuffixOf? ParseSuffix(Expr contained, Expr str) {
        var c = TryParseStr(contained);
        if (c is null)
            return null;
        var s = TryParseStr(str);
        if (s is null)
            return null;
        var ss = MkString(s);
        var sc = MkString(c);
        return new StrSuffixOf(sc, ss, false);
    }

    public StrContains? ParseContains(Expr str, Expr contained) {
        var s = TryParseStr(str);
        if (s is null)
            return null;
        var c = TryParseStr(contained);
        if (c is null)
            return null;
        var ss = MkString(s);
        var sc = MkString(c);
        return new StrContains(ss, sc, false);
    }

    public List<StrToken>? TryParseStr(Expr expr) {
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
                return res;
            }
            if (IsPower(f)) {
                var @base = TryParseStr(expr.Arg(0));
                if (@base is null)
                    return null;
                PDD<BigInteger>? p = TryParseInt((IntExpr)expr.Arg(1));
                if (p is null)
                    return null;
                return [new PowerToken(MkString(@base), p)];
            }
            if (IsStrAt(f)) {
                var @base = TryParseStr(expr.Arg(0));
                if (@base is null)
                    return null;
                PDD<BigInteger>? at = TryParseInt((IntExpr)expr.Arg(1));
                if (at is null)
                    return null;
                return [new StrAtToken(MkString(@base), at)];
            }
            if (IsSubstring(f)) {
                var @base = TryParseStr(expr.Arg(0));
                if (@base is null)
                    return null;
                PDD<BigInteger>? from = TryParseInt((IntExpr)expr.Arg(1));
                if (from is null)
                    return null;
                PDD<BigInteger>? len = TryParseInt((IntExpr)expr.Arg(2));
                if (len is null)
                    return null;
                return [new SubStrToken(MkString(@base), from, len)];
            }
            if (ExprToStrToken.TryGetValue(expr, out StrToken? s))
                return [s];
        }
        else if (expr.Sort is SeqSort) {
            // Native Z3
            if (expr.IsString)
                return expr.String.Select(o => (StrToken)new CharToken(o)).ToList();
            if (expr.IsConst)
                return [GetOrCreateStrVar(f.Name.ToString())];
            if (expr.IsConcat) {
                List<StrToken> r = [];
                foreach (var arg in expr.Args) {
                    var q = TryParseStr(arg);
                    if (q is null)
                        return null;
                    r.AddRange(q);
                }
                return r;
            }
            if (expr.IsAt) {
                var s = TryParseStr(expr.Args[0]);
                if (s is null)
                    return null;
                PDD<BigInteger>? p = TryParseInt((IntExpr)expr.Args[1]);
                if (p is null)
                    return null;
                return [new StrAtToken(MkString(s), p)];
            }
            if (expr.IsExtract) {
                var @base = TryParseStr(expr.Arg(0));
                if (@base is null)
                    return null;
                PDD<BigInteger>? from = TryParseInt((IntExpr)expr.Arg(1));
                if (from is null)
                    return null;
                PDD<BigInteger>? len = TryParseInt((IntExpr)expr.Arg(2));
                if (len is null)
                    return null;
                return [new SubStrToken(MkString(@base), from, len)];
            }
        }
        throw new NotSupportedException(f.Name.ToString());
    }

    public PDD<BigInteger>? TryParseInt(IntExpr expr) {
        if (expr.Sort is not IntSort)
            return null;
        if (expr is IntNum num)
            return IntPDDManager.MkPDD(num.BigInteger);
        if (expr.FuncDecl.Equals(LenFct) || expr.IsLength) {
            var str = TryParseStr(expr.Arg(0));
            return str is null ? null : LenVar.MkLenPoly(str, this);
        }
        if (expr.FuncDecl.Equals(IndexOfFct) || expr.IsIndex) {
            if (expr.NumArgs != 3)
                return null;
            var str = TryParseStr(expr.Arg(0));
            if (str is null)
                return null;
            var contained = TryParseStr(expr.Arg(1));
            if (contained is null)
                return null;
            var start = TryParseInt((IntExpr)expr.Arg(2));
            return start is null ? null : IntPDDManager.MkPDD(new IndexOfVar(MkString(str), MkString(contained), start));
        }
        if (ExprToIntToken.TryGetValue(expr, out var v))
            return IntPDDManager.MkPDD((IntVar)v);
        if (expr.IsAdd) {
            var polys = new PDD<BigInteger>[expr.NumArgs];
            for (uint i = 0; i < expr.NumArgs; i++) {
                var p = TryParseInt((IntExpr)expr.Arg(i));
                if (p is null)
                    return null;
                polys[i] = p;
            }
            if (polys.Length == 0)
                return ZeroInt;
            var poly = polys[0];
            for (int i = 1; i < polys.Length; i++) {
                poly = poly.Add(polys[i]);
            }
            return poly;
        }
        if (expr.IsSub) {
            // What if we have more than two arguments?
            Debug.Assert(expr.NumArgs <= 2);
            var polys = new PDD<BigInteger>[expr.NumArgs];
            for (uint i = 0; i < expr.NumArgs; i++) {
                var p = TryParseInt((IntExpr)expr.Arg(i));
                if (p is null)
                    return null;
                polys[i] = p;
            }
            if (polys.Length == 0)
                return ZeroInt;
            var poly = polys[0];
            for (int i = 1; i < polys.Length; i++) {
                poly = poly.Sub(polys[i]);
            }
            return poly;
        }
        if (expr.IsMul) {
            var polys = new PDD<BigInteger>[expr.NumArgs];
            for (uint i = 0; i < expr.NumArgs; i++) {
                var p = TryParseInt((IntExpr)expr.Arg(i));
                if (p is null)
                    return null;
                polys[i] = p;
            }
            if (polys.Length == 0)
                return OneInt;
            var poly = polys[0];
            for (int i = 1; i < polys.Length; i++) {
                poly = PDD<BigInteger>.Mul(poly, polys[i]);
            }
            return poly;
        }
        throw new NotSupportedException(expr.FuncDecl.Name.ToString());
    }
}