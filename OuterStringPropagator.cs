using System.Diagnostics;
using Microsoft.Z3;
using StringBreaker.Constraints;
using StringBreaker.Constraints.ConstraintElement;
using StringBreaker.Constraints.ConstraintElement.AuxConstraints;
using StringBreaker.IntUtils;
using StringBreaker.MiscUtils;
using StringBreaker.Tokens;
using StringBreaker.Tokens.AuxTokens;

namespace StringBreaker;

public class OuterStringPropagator : UserPropagator {

    bool disposed;
    public readonly Context Ctx;
    public readonly Solver Solver;
    public readonly Sort StringSort;
    public readonly FuncDecl ConcatFct;
    public readonly FuncDecl PowerFct;

    public readonly FuncDecl LenFct;

    public readonly Dictionary<CharToken, ParikhInfo> ParikInfo = [];
    public readonly Dictionary<FuncDecl, InvParikhInfo> InvParikInfo = [];

    public readonly Expr Epsilon;

    // The easy functions
    public readonly FuncDecl StrAtFct;
    public readonly FuncDecl PrefixOfFct;
    public readonly FuncDecl SuffixOfFct;
    public readonly FuncDecl SubstringFct;

    // The tricky ones
    // contains, indexOf, (replace, replaceAll)
    public readonly FuncDecl ContainsFct;
    public readonly FuncDecl IndexOfFct;

    public readonly Dictionary<(StrToken v, int modifications), Expr> StrTokenToExpr = [];
    public readonly Dictionary<Expr, StrToken> ExprToStrToken = [];

    public readonly Dictionary<IntVar, IntExpr> IntTokenToExpr = [];
    public readonly Dictionary<IntExpr, IntVar> ExprToIntToken = [];

    readonly UndoStack undoStack = new();

    public readonly NielsenGraph Graph;
    public NielsenNode Root => Graph.Root;

    List<(Expr lhs, Expr rhs)> reportedEqs = [];
    List<BoolExpr> reportedFixed = [];

    public OuterStringPropagator(Solver solver) : base(solver) {
        Solver = solver;
        Ctx = solver.Context;

        Graph = new NielsenGraph(this);

        StringSort = Ctx.MkUninterpretedSort("Str");
        Epsilon = Ctx.MkUserPropagatorFuncDecl("epsilon", [], StringSort).Apply();
        ConcatFct = Ctx.MkUserPropagatorFuncDecl("concat", [StringSort, StringSort], StringSort);
        PowerFct = Ctx.MkUserPropagatorFuncDecl("power", [StringSort, Ctx.IntSort], StringSort);
        LenFct = Ctx.MkUserPropagatorFuncDecl("len", [StringSort], Ctx.IntSort);

        StrAtFct = Ctx.MkUserPropagatorFuncDecl("strAt", [StringSort], StringSort);
        PrefixOfFct = Ctx.MkUserPropagatorFuncDecl("prefixOf", [StringSort, StringSort], Ctx.BoolSort);
        SuffixOfFct = Ctx.MkUserPropagatorFuncDecl("suffixOf", [StringSort, StringSort], Ctx.BoolSort);
        SubstringFct = Ctx.MkUserPropagatorFuncDecl("subStr", [StringSort, Ctx.IntSort, Ctx.IntSort], StringSort);
        
        ContainsFct = Ctx.MkUserPropagatorFuncDecl("contains", [StringSort, StringSort], Ctx.BoolSort);
        IndexOfFct = Ctx.MkUserPropagatorFuncDecl("indexOf", [StringSort, StringSort, Ctx.IntSort], Ctx.IntSort);

        Fixed = FixedCB;
        Created = CreatedCB;
        Eq = EqCB;
        Final = FinalCB;
    }

    public override void Dispose() {
        if (disposed)
            return;
        disposed = true;
        StrTokenToExpr.Clear();
        ExprToIntToken.Clear();
        StrVarToken.DisposeAll();
        base.Dispose();
    }

    public Expr? GetCachedStrExpr(StrToken t) {
        if (t is not NamedStrToken n || !Graph.CurrentModificationCnt.TryGetValue(n, out int mod))
            mod = 0;
        return StrTokenToExpr.GetValueOrDefault((t, mod));
    }

    public IntExpr? GetCachedIntExpr(IntVar t) => IntTokenToExpr.GetValueOrDefault(t);

    public void SetCachedExpr(StrToken t, Expr e) {
        if (t is not NamedStrToken n || !Graph.CurrentModificationCnt.TryGetValue(n, out int mod))
            mod = 0;
        StrTokenToExpr.Add((t, mod), e);
        ExprToStrToken.Add(e, t);
    }

    public void SetCachedExpr(IntVar t, IntExpr e) {
        IntTokenToExpr.Add(t, e);
        ExprToIntToken.Add((IntExpr)e.Dup(), t);
    }

    public ParikhInfo GetParikhInfo(CharToken c) {
        if (!ParikInfo.TryGetValue(c, out ParikhInfo? info)) {
            info = new ParikhInfo(c, this);
            ParikInfo.Add(c, info);
        }
        return info;
    }

    Expr GetFreshAuxStr() {
        FuncDecl f = Ctx.MkFreshConstDecl("x", StringSort);
        Expr e = Ctx.MkUserPropagatorFuncDecl(f.Name.ToString(), [], StringSort).Apply();
        return e;
    }

    public IntExpr MkLen(Expr e) =>
        (IntExpr)LenFct.Apply(e);

    public IntExpr MkParikh(CharToken c, Expr e) {
        var info = GetParikhInfo(c);
        return (IntExpr)info.Total.Apply(e);
    }

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

    public override void Push() {
        Log.WriteLine("Push " + undoStack.Level);
        undoStack.Push();
    }

    public override void Pop(uint n) {
        try {
            Log.WriteLine("Pop to " + (undoStack.Level - n));
            undoStack.Pop((int)n);
        }
        catch (Exception ex) {
            Console.WriteLine("Exception (Pop): " + ex.Message);
        }
    }

    int fixedCnt;

    void FixedCB(Expr e, Expr valExpr) {
        try {
            Debug.Assert(valExpr.IsTrue || valExpr.IsFalse);
            fixedCnt++;
            bool val = valExpr.IsTrue;

            var f = e.FuncDecl;
            if (f.Equals(PrefixOfFct)) {
                
                Expr u = e.Arg(0);
                Expr v = e.Arg(1);
                Expr x = GetFreshAuxStr();

                if (val) {
                    // e := prefixOf(u, v)
                    // e |- v = ux
                    Propagate([e], Ctx.MkEq(v, MkConcat(u, x)));
                    return;
                }
                // e :=: !prefixOf(u, v)
                // e |- |u| > |v| || (v = xy && |x| = |u| && x != u)
                IntExpr lenU = MkLen(u);
                IntExpr lenV = MkLen(v);
                Expr y = GetFreshAuxStr();
                Propagate([e],
                    Ctx.MkOr(
                        Ctx.MkGt(lenU, lenV),
                        Ctx.MkAnd(
                            Ctx.MkEq(v, MkConcat(x, y)),
                            Ctx.MkEq(MkLen(x), MkLen(u)),
                            Ctx.MkNot(Ctx.MkEq(u, x))
                        )
                    )
                );
                return;
            }
            if (f.Equals(SuffixOfFct)) {

                Expr u = e.Arg(0);
                Expr v = e.Arg(1);
                Expr x = GetFreshAuxStr();

                if (val) {
                    // e := suffixOf(u, v)
                    // e |- v = xu
                    Propagate([e], Ctx.MkEq(v, MkConcat(x, u)));
                    return;
                }
                // e :=: !suffixOf(u, v)
                // e |- |u| > |v| || (v = yx && |x| = |u| && x != u)
                IntExpr lenU = MkLen(u);
                IntExpr lenV = MkLen(v);
                Expr y = GetFreshAuxStr();
                Propagate([e],
                    Ctx.MkOr(
                        Ctx.MkGt(lenU, lenV),
                        Ctx.MkAnd(
                            Ctx.MkEq(v, MkConcat(y, x)),
                            Ctx.MkEq(MkLen(x), MkLen(u)),
                            Ctx.MkNot(Ctx.MkEq(u, x))
                        )
                    )
                );
                return;
            }
            if (f.Equals(ContainsFct)) {
                if (!val) {
                    reportedFixed.Add((BoolExpr)e);
                    undoStack.Add(() => reportedFixed.Pop());
                    // TODO
                    throw new NotImplementedException("!contains");
                    return;
                }
                // e := contains(u, v)
                // e |- |v| = 0 || u = xvy (the first case only to speed up)
                Expr u = e.Arg(0);
                Expr v = e.Arg(1);
                IntExpr lenV = MkLen(v);
                Expr x = GetFreshAuxStr();
                Expr y = GetFreshAuxStr();
                Propagate([e],
                    Ctx.MkOr(
                        Ctx.MkEq(lenV, Ctx.MkInt(0)),
                        Ctx.MkEq(u, MkConcat(x, MkConcat(v, y)))
                    )
                );
                return;
            }

            Log.WriteLine($"Fixed ({fixedCnt}): {StrToken.ExprToStr(Graph, e)} = {valExpr}");
            Console.WriteLine($"Unexpected and ignored: {StrToken.ExprToStr(Graph, e)} = {valExpr}");
        }
        catch (Exception ex) {
            Console.WriteLine("Exception (Fixed): " + ex.Message);
        }
    }

    void CreatedCB(Expr e) {

        // Just rewrite complicated function symbols
        if (e.Sort is not BoolSort && !e.Sort.Equals(StringSort))
            return;

        var f = e.FuncDecl;

        if (f.Equals(StrAtFct)) {
            // e := strAt(u, i)
            // (i < 0 || i >= |u|) => |e| = 0
            // !(i < 0 || i >= |u|) => (|e| = 1 && u = xey && |x| = i)
            Expr u = e.Arg(0);
            IntExpr i = (IntExpr)e.Arg(1);
            IntExpr lenU = MkLen(u);
            IntExpr lenE = MkLen(e);
            IntExpr zero = Ctx.MkInt(0);
            IntExpr one = Ctx.MkInt(1);
            BoolExpr outsideBounds = Ctx.MkOr(
                Ctx.MkLt(i, Ctx.MkInt(0)),
                Ctx.MkGe(i, lenU)
            );
            Expr x = GetFreshAuxStr();
            Expr y = GetFreshAuxStr();
            IntExpr lenX = MkLen(x);
            Propagate([], Ctx.MkImplies(outsideBounds, Ctx.MkEq(lenE, zero)));
            Propagate([],
                Ctx.MkImplies(Ctx.MkNot(outsideBounds),
                    Ctx.MkAnd(
                        Ctx.MkEq(lenE, one),
                        Ctx.MkEq(lenX, i),
                        Ctx.MkEq(u, MkConcat(x, MkConcat(e, y)))
                    )
                )
            );
            return;
        }
        if (f.Equals(SubstringFct)) {
            // e := subStr(u, from, len)
            // (from < 0 || len <= 0 || from >= |u|) => |e| = 0
            // (from >= 0 && len > 0 && from < |u| && from + len >= |u|) =>
            //      (u = xe && |x| = from && |e| = |u| - from)
            // (from >= 0 && len > 0 && from + len < |u|) =>
            //      (u = xey && |x| = from && |e| = len)
            Expr u = e.Arg(0);
            IntExpr from = (IntExpr)e.Arg(1);
            IntExpr len = (IntExpr)e.Arg(2);
            IntExpr lenU = MkLen(u);
            IntExpr lenE = MkLen(e);
            IntExpr zero = Ctx.MkInt(0);
            Propagate([],
                Ctx.MkImplies(
                    Ctx.MkOr(
                        Ctx.MkLt(from, zero),
                        Ctx.MkLe(len, zero),
                        Ctx.MkGe(from, lenU)
                    ),
                    Ctx.MkEq(lenE, zero)
                )
            );
            Expr x = GetFreshAuxStr();
            Expr y = GetFreshAuxStr();
            IntExpr lenX = MkLen(x);
            Propagate([],
                Ctx.MkImplies(
                    Ctx.MkAnd(
                        Ctx.MkGe(from, zero),
                        Ctx.MkGt(len, zero),
                        Ctx.MkLt(from, lenU),
                        Ctx.MkGe(Ctx.MkAdd(from, len), lenU)
                    ),
                    Ctx.MkAnd(
                        Ctx.MkEq(u, MkConcat(x, e)),
                        Ctx.MkEq(lenX, from),
                        Ctx.MkEq(lenE, Ctx.MkSub(lenU, from))
                    )
                )
            );
            Propagate([],
                Ctx.MkImplies(
                    Ctx.MkAnd(
                        Ctx.MkGe(from, zero),
                        Ctx.MkGt(len, zero),
                        Ctx.MkLt(Ctx.MkAdd(from, len), lenU)
                    ),
                    Ctx.MkAnd(
                        Ctx.MkEq(u, MkConcat(x, MkConcat(e, y))),
                        Ctx.MkEq(lenX, from),
                        Ctx.MkEq(lenE, len)
                    )
                )
            );
            return;
        }
        if (f.Equals(IndexOfFct)) {
            // e := indexOf(u, v, from)
            // from < 0 => e = -1
            // from > |u| + |v| => e = -1
            // !contains(u, v) => e = -1
            // (from >= 0 && from <= |u| && |v| = 0) => e = from
            // (from >= 0 && from <= |u| + |v| && |v| > 0) =>
            //      (0 <= e && e <= |u| - |v| && u = xvy && |x| = from && !contains(subStr(xv, 0, |x| + |v| - 1), v))
            Expr u = e.Arg(0);
            Expr v = e.Arg(1);
            IntExpr from = (IntExpr)e.Arg(2);
            IntExpr lenU = MkLen(u);
            IntExpr lenV = MkLen(v);
            IntExpr zero = Ctx.MkInt(0);
            IntExpr negOne = Ctx.MkInt(-1);
            Expr x = GetFreshAuxStr();
            Expr y = GetFreshAuxStr();
            IntExpr lenX = MkLen(x);
            Propagate([],
                Ctx.MkImplies(
                    Ctx.MkLt(from, zero),
                    Ctx.MkEq(e, negOne)
                )
            );
            Propagate([],
                Ctx.MkImplies(
                    Ctx.MkGt(from, Ctx.MkAdd(lenU, lenV)),
                    Ctx.MkEq(e, negOne)
                )
            );
            Propagate([],
                Ctx.MkImplies(
                    Ctx.MkNot((BoolExpr)ContainsFct.Apply(u, v)),
                    Ctx.MkEq(e, negOne)
                )
            );
            Propagate([],
                Ctx.MkImplies(
                    Ctx.MkAnd(
                        Ctx.MkGe(from, zero),
                        Ctx.MkLe(from, lenU),
                        Ctx.MkEq(lenV, zero)
                    ),
                    Ctx.MkEq(e, from)
                )
            );
            Propagate([],
                Ctx.MkImplies(
                    Ctx.MkAnd(
                        Ctx.MkGe(from, zero),
                        Ctx.MkLe(from, Ctx.MkAdd(lenU, lenV)),
                        Ctx.MkGt(lenV, zero)
                    ),
                    Ctx.MkAnd(
                        Ctx.MkGe((IntExpr)e, zero),
                        Ctx.MkLe((IntExpr)e, Ctx.MkSub(lenU, lenV)),
                        Ctx.MkEq(u, MkConcat(x, MkConcat(v, y))),
                        Ctx.MkEq(lenX, from),
                        Ctx.MkNot(
                            (BoolExpr)ContainsFct.Apply(
                                SubstringFct.Apply(MkConcat(x, v), zero, Ctx.MkAdd(lenX, lenV, negOne)), v)
                        )
                    )
                )
            );
            return;
        }
    }

    static int eqCount;

    void EqCB(Expr e1, Expr e2) {
        try {
            if (e1.Equals(e2))
                return;

            if (!e1.Sort.Equals(StringSort))
                return;

            eqCount++;
            Log.WriteLine($"Eq ({eqCount}): {StrToken.ExprToStr(Graph, e1)} = {StrToken.ExprToStr(Graph, e2)}");

            Str? s1r = TryParseStr(e1);
            Str? s2r = TryParseStr(e2);
            Debug.Assert(s1r is not null);
            Debug.Assert(s2r is not null);

            if (s1r.Count > s2r.Count)
                (s1r, s2r) = (s2r, s1r);

            Debug.Assert(s1r is not null);
            Debug.Assert(s2r is not null);

            Console.WriteLine($"Eq: {s1r.ToString(Graph)} = {s2r.ToString(Graph)}");

            if (s1r.Count >= 2 && s2r.Count >= 2) {
#if false
            // or some other condition to only do this if really necessary
            HashSet<NonTermToken> vars = [];
            HashSet<CharToken> alph = [];
            s1.CollectSymbols(vars, alph);
            s2.CollectSymbols(vars, alph);

            HashSet<uint> mod = [];
            /*HashSet<uint> modRaw = [];
            // Get prime number decomposition of the number of occurrences of each variable
            foreach (var v in vars) {
                // TODO: So far I ignore occurrences in power (though; I do not know if we really want them in there anyway)
                uint cnt1 = (uint)s1.Count(o => o is NonTermToken v2 && v2.Equals(v));
                modRaw.Plus(cnt1);
                uint cnt2 = (uint)s2.Count(o => o is NonTermToken v2 && v2.Equals(v));
                modRaw.Plus(cnt2);
            }

            foreach (uint m in modRaw) {
                uint n = m;
                if (n <= 1)
                    continue;
                for (int i = 2; i <= n; i++) {
                    if (n % i == 0) {
                        while (n % i == 0) {
                            n /= (uint)i;
                        }
                        mod.Plus((uint)i);
                    }
                }
            }*/

            // TODO: For now just try all; also enumerating primes can be optimized...
            uint len = Math.Max((uint)s1.Count, (uint)s2.Count);
            for (uint m = 2; m <= len; m++) {
                uint n = m;
                for (uint i = 2; i <= n; i++) {
                    if (n % i == 0) {
                        while (n % i == 0) {
                            n /= i;
                        }
                        mod.Plus(i);
                    }
                }
            }

            foreach (var c in alph) {
                var info = GetParikhInfo(c);
                Propagate([], eqPair, Ctx.MkEq(info.Total.Apply(e1), info.Total.Apply(e2)));
                foreach (uint m in mod) {
                    var res = info.GetResidual(m, this);
                    for (int r = 0; r < m; r++) {
                        Propagate([], eqPair, Ctx.MkEq(res.Apply(Ctx.MkInt(r), e1), res.Apply(Ctx.MkInt(r), e2)));
                    }
                }
            }
#endif
            }
            var eq = new StrEq(s1r, s2r);
            HashSet<NamedStrToken> vars = [];
            HashSet<SymCharToken> sChars = [];
            HashSet<IntVar> iVars = [];
            HashSet<CharToken> alph = [];
            eq.CollectSymbols(vars, sChars, iVars, alph);

            Root.AddConstraints(eq); // u = v
            Root.AddConstraints(new IntEq(LenVar.MkLenPoly(s1r), LenVar.MkLenPoly(s2r))); // u = v => |u| = |v|
            foreach (var a in alph) {
                Root.AddConstraints(new IntEq(Parikh.MkParikhPoly(a, s1r), Parikh.MkParikhPoly(a, s2r))); // u = v => |u|_a = |v|_a
            }
            reportedEqs.Add((e1, e2));
            undoStack.Add(() => reportedEqs.Pop());
        }
        catch (Exception ex) {
            Console.WriteLine("Exception (Eq): " + ex.Message);
        }
    }

    int finalCnt;

    void FinalCB() {
        try {
            finalCnt++;
            Log.WriteLine("Final (" + finalCnt + ")");
            var res = Graph.Check();
            if (res) 
                return;
            EqualityPairs pair = new();
            foreach (var (lhs, rhs) in reportedEqs) {
                pair.Add(lhs, rhs);
            }
            Propagate(reportedFixed.ToArray(), pair, Ctx.MkFalse());
        }
        catch (Exception ex) {
            Console.WriteLine("Exception (Final): " + ex.Message);
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
        FuncDecl decl = expr.FuncDecl;
        if (expr.Sort.Equals(StringSort)) {
            // Custom Z3
            if (expr.Equals(Epsilon))
                return [];
            if (decl.Equals(ConcatFct)) {
                List<StrToken> res = [];
                for (uint i = 0; i < expr.NumArgs; i++) {
                    if (TryParseStr(expr.Arg(i)) is not { } str)
                        return null;
                    res.AddRange(str);
                }
                return new Str(res);
            }
            if (decl.Equals(PowerFct)) {
                Str? @base = TryParseStr(expr.Arg(0));
                if (@base is null)
                    return null;
                Poly? p = TryParseInt((IntExpr)expr.Arg(1));
                if (p is null)
                    return null;
                return new Str([new PowerToken(@base, p)]);
            }
            if (decl.Equals(StrAtFct)) {
                Str? @base = TryParseStr(expr.Arg(0));
                if (@base is null)
                    return null;
                Poly? at = TryParseInt((IntExpr)expr.Arg(1));
                if (at is null)
                    return null;
                return [new StrAtToken(@base, at)];
            }
            if (decl.Equals(SubstringFct)) {
                Str? @base = TryParseStr(expr.Arg(0));
                if (@base is null)
                    return null;
                Poly? from = TryParseInt((IntExpr)expr.Arg(1));
                if (from is null)
                    return null;
                Poly? len = TryParseInt((IntExpr)expr.Arg(2));
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
                return new Str([StrVarToken.GetOrCreate(decl.Name.ToString())]);
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
                Poly? p = TryParseInt((IntExpr)expr.Args[1]);
                if (p is null)
                    return null;
                return [new StrAtToken(s, p)];
            }
            if (expr.IsExtract) {
                Str? @base = TryParseStr(expr.Arg(0));
                if (@base is null)
                    return null;
                Poly? from = TryParseInt((IntExpr)expr.Arg(1));
                if (from is null)
                    return null;
                Poly? len = TryParseInt((IntExpr)expr.Arg(2));
                if (len is null)
                    return null;
                return [new SubStrToken(@base, from, len)];
            }
        }
        throw new NotSupportedException(decl.Name.ToString());
    }

    public Poly? TryParseInt(IntExpr expr) {
        if (expr.Sort is not IntSort)
            return null;
        if (expr is IntNum num)
            return new Poly(num.BigInteger);
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
            Poly? start = TryParseInt((IntExpr)expr.Arg(2));
            return start is null ? null : new Poly(new IndexOfVar(str, contained, start));
        }
        if (InvParikInfo.TryGetValue(expr.FuncDecl, out var parikhInfo)) {
            var s = TryParseStr((IntExpr)expr.Arg(0));
            if (s is null)
                return null;
            if (parikhInfo.IsTotal)
                return Parikh.MkParikhPoly(parikhInfo.Info.Char, s);
            throw new NotImplementedException();
        }
        if (ExprToIntToken.TryGetValue(expr, out var v))
            return new Poly(v);
        if (expr.IsAdd) {
            var polys = new Poly[expr.NumArgs];
            for (uint i = 0; i < expr.NumArgs; i++) {
                Poly? p = TryParseInt((IntExpr)expr.Arg(i));
                if (p is null)
                    return null;
                polys[i] = p;
            }
            if (polys.Length == 0)
                return new Poly();
            Poly poly = polys[0];
            for (int i = 1; i < polys.Length; i++) {
                poly.Plus(polys[i]);
            }
            return poly;
        }
        if (expr.IsSub) {
            // What if we have more than two arguments?
            Debug.Assert(expr.NumArgs <= 2);
            var polys = new Poly[expr.NumArgs];
            for (uint i = 0; i < expr.NumArgs; i++) {
                Poly? p = TryParseInt((IntExpr)expr.Arg(i));
                if (p is null)
                    return null;
                polys[i] = p;
            }
            if (polys.Length == 0)
                return new Poly();
            Poly poly = polys[0];
            for (int i = 1; i < polys.Length; i++) {
                poly.Sub(polys[i]);
            }
            return poly;
        }
        if (expr.IsMul) {
            var polys = new Poly[expr.NumArgs];
            for (uint i = 0; i < expr.NumArgs; i++) {
                Poly? p = TryParseInt((IntExpr)expr.Arg(i));
                if (p is null)
                    return null;
                polys[i] = p;
            }
            if (polys.Length == 0)
                return new Poly(1);
            Poly poly = polys[0];
            for (int i = 1; i < polys.Length; i++) {
                poly = Poly.Mul(poly, polys[i]);
            }
            return poly;
        }
        throw new NotSupportedException(expr.FuncDecl.Name.ToString());
    }

    public Expr CreateFresh(Expr e, Dictionary<Expr, Expr> oldToNew) {
        if (e.IsConst) {
            if (oldToNew.TryGetValue(e, out Expr? v))
                return v;
            Expr n = e.Context.MkFreshConst(e.FuncDecl.Name.ToString(), e.Sort);
            oldToNew.Add(e.Dup(), n.Dup());
            return n;
        }
        return e.FuncDecl.Apply(e.Args.Select(o => CreateFresh(o, oldToNew)).ToArray());
    }

    public bool GetModel(out Interpretation itp) {
        
        HashSet<NamedStrToken> initSVars = [];
        HashSet<SymCharToken> initSymChars = [];
        HashSet<IntVar> initIVars = [];
        HashSet<CharToken> initAlphabet = [];
        Graph.Root.CollectSymbols(initSVars, initSymChars, initIVars, initAlphabet);

        Debug.Assert(Graph.SatNodes.IsNonEmpty());
        var satNode = Graph.SatNodes[0];

        if (satNode.Parent is not null)
            Graph.SubSolver.Check(satNode.Parent!.Assumption);
        else
            Graph.SubSolver.Check();

        var model = Graph.SubSolver.Model;
        itp = new Interpretation();
        foreach (var c in model.Consts) {
            if (c.Key.Apply() is not IntExpr i)
                continue;
            if (!ExprToIntToken.TryGetValue(i, out var v))
                continue;
            itp.Add(v, ((IntNum)c.Value).BigInteger);
            if (!satNode.ConsistentIntVal(v, ((IntNum)c.Value).BigInteger))
                Console.WriteLine("Z3 Model is not consistent with internal bounds on " + v);
        }
        Debug.Assert(model is not null);
        
        foreach (var parent in satNode.EnumerateParents()) {
            foreach (var subst in parent.Subst) {
                subst.AddToInterpretation(itp);
            }
        }

        if (Options.ModelCompletion)
            itp.Complete(initAlphabet);

        bool modelCheck = true;
        var allConstraints = Root.AllConstraints.Select(o => o.Clone());
        foreach (var cnstr in allConstraints) {
            var orig = cnstr.Clone();
            cnstr.Apply(itp);
            BacktrackReasons reason = BacktrackReasons.Unevaluated;
            if (cnstr.Simplify(satNode, [], [], ref reason) == SimplifyResult.Satisfied)
                continue;
            modelCheck = false;
            Console.WriteLine("Constraint " + orig + " not satisfied: " + cnstr);
        }

        Console.WriteLine(modelCheck ? "Model seems fine" : "ERROR: Created invalid model");

        itp.ProjectTo(initSVars, initSymChars, initIVars);

        return modelCheck;
    }
}