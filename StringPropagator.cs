using System.Diagnostics;
using System.IO;
using Microsoft.Z3;
using StringBreaker.Constraints;
using StringBreaker.Constraints.ConstraintElement;
using StringBreaker.Constraints.Modifier;
using StringBreaker.IntUtils;
using StringBreaker.MiscUtils;
using StringBreaker.Tokens;

namespace StringBreaker;

public abstract class StringPropagator : UserPropagator {

    public readonly Context Ctx;
    public readonly Solver Solver;
    public readonly ExpressionCache Cache;

    public abstract NielsenGraph Graph { get; }

    protected readonly UndoStack undoStack = new();

    protected StringPropagator(Solver solver, ExpressionCache cache) : base(solver) {
        Solver = solver;
        Ctx = solver.Context;
        Cache = cache;

        Fixed = FixedCB;
        Created = CreatedCB;
        Eq = EqCB;
        Diseq = DisEqCB;
    }

    StrVarToken GetFreshAuxStr() => StrVarToken.GetOrCreate("x");

    public override void Push() {
        if (Graph.OuterPropagator.Cancel)
            throw new SolverTimeoutException();
        Log.WriteLine("Push " + undoStack.Level);
        undoStack.Push();
    }

    public override void Pop(uint n) {
        if (Graph.OuterPropagator.Cancel)
            throw new SolverTimeoutException();
        try {
            Log.WriteLine("Pop to " + (undoStack.Level - n));
            undoStack.Pop((int)n);
        }
        catch (Exception ex) {
            Console.WriteLine("Exception (Pop): " + ex.Message);
        }
    }

    protected virtual void GotNegContains(BoolExpr e) {}
    protected virtual void GotPathLiteral(BoolExpr e, bool val) {}

    int fixedCnt;

    void FixedCB(Expr e, Expr valExpr) {
        try {
            Debug.Assert(valExpr.IsTrue || valExpr.IsFalse);
            fixedCnt++;
            bool val = valExpr.IsTrue;

            var f = e.FuncDecl;
            if (Cache.IsPrefixOf(f)) {
                
                Expr u = e.Arg(0);
                Expr v = e.Arg(1);
                Expr x = GetFreshAuxStr().ToExpr(Graph);

                if (val) {
                    // e := prefixOf(u, v)
                    // e |- v = ux
                    Propagate([e], Ctx.MkEq(v, Cache.MkConcat(u, x)));
                    return;
                }
                // e :=: !prefixOf(u, v)
                // e |- |u| > |v| || (v = xy && |x| = |u| && x != u)
                IntExpr lenU = Cache.MkLen(u);
                IntExpr lenV = Cache.MkLen(v);
                Expr y = GetFreshAuxStr().ToExpr(Graph);
                Propagate([e],
                    Ctx.MkOr(
                        Ctx.MkGt(lenU, lenV),
                        Ctx.MkAnd(
                            Ctx.MkEq(v, Cache.MkConcat(x, y)),
                            Ctx.MkEq(Cache.MkLen(x), Cache.MkLen(u)),
                            Ctx.MkNot(Ctx.MkEq(u, x))
                        )
                    )
                );
                return;
            }
            if (Cache.IsSuffixOf(f)) {

                Expr u = e.Arg(0);
                Expr v = e.Arg(1);
                Expr x = GetFreshAuxStr().ToExpr(Graph);

                if (val) {
                    // e := suffixOf(u, v)
                    // e |- v = xu
                    Propagate([e], Ctx.MkEq(v, Cache.MkConcat(x, u)));
                    return;
                }
                // e :=: !suffixOf(u, v)
                // e |- |u| > |v| || (v = yx && |x| = |u| && x != u)
                IntExpr lenU = Cache.MkLen(u);
                IntExpr lenV = Cache.MkLen(v);
                Expr y = GetFreshAuxStr().ToExpr(Graph);
                Propagate([e],
                    Ctx.MkOr(
                        Ctx.MkGt(lenU, lenV),
                        Ctx.MkAnd(
                            Ctx.MkEq(v, Cache.MkConcat(y, x)),
                            Ctx.MkEq(Cache.MkLen(x), Cache.MkLen(u)),
                            Ctx.MkNot(Ctx.MkEq(u, x))
                        )
                    )
                );
                return;
            }
            if (Cache.IsContains(f)) {
                if (!val) {
                    GotNegContains((BoolExpr)e);
                    return;
                }
                // e := contains(u, v)
                // e |- |v| = 0 || u = xvy (the first case only to speed up)
                Expr u = e.Arg(0);
                Expr v = e.Arg(1);
                IntExpr lenV = Cache.MkLen(v);
                Expr x = GetFreshAuxStr().ToExpr(Graph);
                Expr y = GetFreshAuxStr().ToExpr(Graph);
                Propagate([e],
                    Ctx.MkOr(
                        Ctx.MkEq(lenV, Ctx.MkInt(0)),
                        Ctx.MkEq(u, Cache.MkConcat(x, Cache.MkConcat(v, y)))
                    )
                );
                return;
            }

            GotPathLiteral((BoolExpr)e, val);
        }
        catch (Exception ex) {
            Console.WriteLine("Exception (Fixed): " + ex.Message);
        }
    }

    void CreatedCB(Expr e) {

        // Just rewrite complicated function symbols
        if (e.Sort is not BoolSort && !e.Sort.Equals(Cache.StringSort) && e.Sort is not IntSort)
            return;

        var f = e.FuncDecl;

        if (Cache.IsStrAt(f)) {
            // e := strAt(u, i)
            // (i < 0 || i >= |u|) => |e| = 0
            // !(i < 0 || i >= |u|) => (|e| = 1 && u = xey && |x| = i)
            Expr u = e.Arg(0);
            IntExpr i = (IntExpr)e.Arg(1);
            IntExpr lenU = Cache.MkLen(u);
            IntExpr lenE = Cache.MkLen(e);
            IntExpr zero = Ctx.MkInt(0);
            IntExpr one = Ctx.MkInt(1);
            BoolExpr outsideBounds = Ctx.MkOr(
                Ctx.MkLt(i, Ctx.MkInt(0)),
                Ctx.MkGe(i, lenU)
            );
            Expr x = GetFreshAuxStr().ToExpr(Graph);
            Expr y = GetFreshAuxStr().ToExpr(Graph);
            IntExpr lenX = Cache.MkLen(x);
            Propagate([], Ctx.MkImplies(outsideBounds, Ctx.MkEq(lenE, zero)));
            Propagate([],
                Ctx.MkImplies(Ctx.MkNot(outsideBounds),
                    Ctx.MkAnd(
                        Ctx.MkEq(lenE, one),
                        Ctx.MkEq(lenX, i),
                        Ctx.MkEq(u, Cache.MkConcat(x, Cache.MkConcat(e, y)))
                    )
                )
            );
            return;
        }
        if (Cache.IsSubstring(f)) {
            // e := subStr(u, from, len)
            // (from < 0 || len <= 0 || from >= |u|) => |e| = 0
            // (from >= 0 && len > 0 && from < |u| && from + len >= |u|) =>
            //      (u = xe && |x| = from && |e| = |u| - from)
            // (from >= 0 && len > 0 && from + len < |u|) =>
            //      (u = xey && |x| = from && |e| = len)
            Expr u = e.Arg(0);
            IntExpr from = (IntExpr)e.Arg(1);
            IntExpr len = (IntExpr)e.Arg(2);
            IntExpr lenU = Cache.MkLen(u);
            IntExpr lenE = Cache.MkLen(e);
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
            Expr x = GetFreshAuxStr().ToExpr(Graph);
            Expr y = GetFreshAuxStr().ToExpr(Graph);
            IntExpr lenX = Cache.MkLen(x);
            Propagate([],
                Ctx.MkImplies(
                    Ctx.MkAnd(
                        Ctx.MkGe(from, zero),
                        Ctx.MkGt(len, zero),
                        Ctx.MkLt(from, lenU),
                        Ctx.MkGe(Ctx.MkAdd(from, len), lenU)
                    ),
                    Ctx.MkAnd(
                        Ctx.MkEq(u, Cache.MkConcat(x, e)),
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
                        Ctx.MkEq(u, Cache.MkConcat(x, Cache.MkConcat(e, y))),
                        Ctx.MkEq(lenX, from),
                        Ctx.MkEq(lenE, len)
                    )
                )
            );
            return;
        }
        if (Cache.IsIndexOf(f)) {
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
            IntExpr lenU = Cache.MkLen(u);
            IntExpr lenV = Cache.MkLen(v);
            IntExpr zero = Ctx.MkInt(0);
            IntExpr negOne = Ctx.MkInt(-1);
            Expr x = GetFreshAuxStr().ToExpr(Graph);
            Expr y = GetFreshAuxStr().ToExpr(Graph);
            IntExpr lenX = Cache.MkLen(x);
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
                    Ctx.MkNot((BoolExpr)Cache.ContainsFct.Apply(u, v)),
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
                        Ctx.MkEq(u, Cache.MkConcat(x, Cache.MkConcat(v, y))),
                        Ctx.MkEq(lenX, from),
                        Ctx.MkNot(
                            (BoolExpr)Cache.ContainsFct.Apply(
                                Cache.SubstringFct.Apply(Cache.MkConcat(x, v), zero, Ctx.MkAdd(lenX, lenV, negOne)), v)
                        )
                    )
                )
            );
            return;
        }
        if (Cache.IsLen(f)) {
            Expr arg0 = e.Arg(0);
            FuncDecl f0 = arg0.FuncDecl;
            if (Cache.IsConcat(f0)) {
                Stack<Expr> args = [];
                args.Push(arg0);
                IntExpr sum = Ctx.MkInt(0);
                while (args.IsNonEmpty()) {
                    var arg = args.Pop();
                    if (Cache.IsConcat(arg.FuncDecl)) {
                        args.Push(arg.Arg(0));
                        args.Push(arg.Arg(1));
                        continue;
                    }
                    sum = (IntExpr)Ctx.MkAdd(sum, Cache.MkLen(arg));
                }
                Propagate([], Ctx.MkEq(e, sum));
                return;
            }
            if (f0.Equals(Cache.Epsilon.FuncDecl)) {
                Propagate([], Ctx.MkEq(e, Ctx.MkInt(0)));
                return;
            }
            if (Cache.IsPower(f0)) {
                Propagate([], Ctx.MkEq(e, Ctx.MkMul(Cache.MkLen(arg0.Arg(0)), (IntExpr)arg0.Arg(1))));
                return;
            }
            if (Cache.ExprToStrToken.TryGetValue(arg0, out var s)) {
                if (s is UnitToken) {
                    Propagate([], Ctx.MkEq(e, Ctx.MkInt(1)));
                    return;
                }
                Debug.Assert(s is NamedStrToken);
                var lenTerm = new LenVar((NamedStrToken)s).ToExpr(Graph);
                Propagate([], Ctx.MkEq((IntExpr)e, lenTerm));
                Propagate([], Ctx.MkGe((IntExpr)e, Ctx.MkInt(0)));
                
                /*if (rewrite.TryGetValue(arg0, out List<Expr>? r)) {
                    foreach (var r0 in r) {
                        EqualityPairs eq = new();
                        eq.Add(arg0, r0);
                        Propagate([], eq, Ctx.MkEq(e, Cache.MkLen(r0)));
                    }
                    return;
                }
                if (!watch.TryGetValue(arg0, out var list)) {
                    Expr arg0d = arg0.Dup();
                    watch.Add(arg0d, list = []);
                    undoStack.Add(() => watch.Remove(arg0d));
                }
                list.Add(e.Dup());
                undoStack.Add(() => list.Pop());*/
            }
            return;
        }
        // if (Cache.InvParikInfo.TryGetValue(f, out var ipi)) {
        //     Expr arg0 = e.Arg(0);
        //     FuncDecl f0 = arg0.FuncDecl;
        //     if (Cache.IsConcat(f0)) {
        //         Stack<Expr> args = [];
        //         args.Push(arg0);
        //         IntExpr sum = Ctx.MkInt(0);
        //         while (args.IsNonEmpty()) {
        //             var arg = args.Pop();
        //             if (Cache.IsConcat(arg.FuncDecl)) {
        //                 args.Push(arg.Arg(0));
        //                 args.Push(arg.Arg(1));
        //                 continue;
        //             }
        //             sum = (IntExpr)Ctx.MkAdd(sum, (IntExpr)ipi.Info.Total.Apply(arg));
        //         }
        //         Propagate([], Ctx.MkEq(e, sum));
        //         return;
        //     }
        //     if (f0.Equals(Cache.Epsilon.FuncDecl)) {
        //         Propagate([], Ctx.MkEq(e, Ctx.MkInt(0)));
        //         return;
        //     }
        //     if (Cache.IsPower(f0)) {
        //         Propagate([], Ctx.MkEq(e, Ctx.MkMul((IntExpr)ipi.Info.Total.Apply(arg0.Arg(0)), (IntExpr)arg0.Arg(1))));
        //         return;
        //     }
        //     if (Cache.ExprToStrToken.TryGetValue(arg0, out var s)) {
        //         if (s is UnitToken) {
        //             Propagate([], Ctx.MkEq(e, Ctx.MkITE(
        //                 Ctx.MkEq(s.ToExpr(Graph), ipi.Info.Char.ToExpr(Graph)),
        //                 Ctx.MkInt(1), Ctx.MkInt(0))));
        //             return;
        //         }
        //         Debug.Assert(s is NamedStrToken);
        //         if (rewrite.TryGetValue(arg0, out var r)) {
        //             foreach (var r0 in r) {
        //                 EqualityPairs eq = new();
        //                 eq.Add(arg0, r0);
        //                 Propagate([], eq, Ctx.MkEq(e, ipi.Info.Total.Apply(r0)));
        //             }
        //             return;
        //         }
        //         Propagate([], Ctx.MkGe((IntExpr)e, Ctx.MkInt(0)));
        //         if (!watch.TryGetValue(arg0, out var list)) {
        //             Expr arg0d = arg0.Dup();
        //             watch.Add(arg0d, list = []);
        //             undoStack.Add(() => watch.Remove(arg0d));
        //         }
        //         list.Add(e.Dup());
        //         undoStack.Add(() => list.Pop());
        //     }
        //     return;
        // }
    }

    protected virtual void AddCharDiseqInternal(DisEq disEq) {}

    void AddCharDiseq(UnitToken u1, UnitToken u2) {
        if (u1 is not SymCharToken o) {
            if (u2 is not SymCharToken)
                return;
            (u1, u2) = (u2, u1);
            o = (SymCharToken)u1;
        }

        AddCharDiseqInternal(new DisEq(o, u2));
    }

    public virtual void EqInternal(Str s1, Expr e1, Str s2, Expr e2) {}

    static int eqCount;

    void EqCB(Expr e1, Expr e2) {
        try {
            if (e1.Equals(e2))
                return;

            if (!e1.Sort.Equals(Cache.StringSort))
                return;

            eqCount++;
            Log.WriteLine($"Eq ({eqCount}): {StrToken.ExprToStr(Graph, e1)} = {StrToken.ExprToStr(Graph, e2)}");

            /*
            if (
                Cache.ExprToStrToken.TryGetValue(e1, out var t1) && t1 is UnitToken c1 &&
                Cache.ExprToStrToken.TryGetValue(e2, out var t2) && t2 is UnitToken c2) {
                if (c1 is CharToken ch1 && c2 is CharToken ch2) {
                    if (ch1.Equals(ch2)) {
                        Debug.Assert(false); // Why would Z3 report this?!
                        return;
                    }
                    EqualityPairs eqJust = new();
                    eqJust.Add(e1, e2);
                    Propagate([], eqJust, Ctx.MkFalse());
                    return;
                }
                AddCharEqInternal(c1, c2);
                return;
            }

            Expr? f = null, t = null; // rewriting t := f (t has to some substitutable token - i.e., everything that is not concatenation or power)
            if (!Cache.ExprToStrToken.TryGetValue(e1, out var s1) || s1 is not NamedStrToken) {
                if (Cache.ExprToStrToken.TryGetValue(e2, out var s2) && s2 is NamedStrToken) {
                    f = e2;
                    t = e1;
                }
            }
            else {
                if (rewrite.ContainsKey(e1)) {
                    if (Cache.ExprToStrToken.TryGetValue(e2, out var s2) && s2 is NamedStrToken) {
                        f = e2;
                        t = e1;
                    }
                }
                else {
                    f = e1;
                    t = e2;
                }
            }
            if (f is not null) {
                Debug.Assert(t is not null);
                Expr fc = f.Dup();
                if (!rewrite.TryGetValue(fc, out var list)) {
                    rewrite.Add(fc, list = []);
                    undoStack.Add(() => rewrite.Remove(fc));
                }
                list.Add(t.Dup());
                undoStack.Add(() => list.Pop());

                var w = watch.GetValueOrDefault(f, []);

                for (int i = 0; i < w.Count; i++) {
                    CreatedCB(w[i]);
                }
            }*/

            Str? s1r = Cache.TryParseStr(e1);
            Str? s2r = Cache.TryParseStr(e2);
            Debug.Assert(s1r is not null);
            Debug.Assert(s2r is not null);

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

            EqInternal(s1r, e1, s2r, e2);
        }
        catch (Exception ex) {
            Console.WriteLine("Exception (Eq): " + ex.Message);
        }
    }

    protected virtual void AddNotEpsilonInternal(Str s) {}

    void DisEqCB(Expr e1, Expr e2) {
        try {
            if (!e1.Sort.Equals(Cache.StringSort))
                return;
            // TODO: Fix for characters. e.g., o1 != o2 clauses infinite recursion!

            if (Cache.Epsilon.Equals(e2))
                (e1, e2) = (e2, e1);

            if (Cache.Epsilon.Equals(e1)) {
                if (Cache.ExprToStrToken.TryGetValue(e2, out var t) && t is UnitToken) {
                    Propagate([], Ctx.MkDistinct(e1, e2));
                    return;
                }
                Propagate([],
                    Ctx.MkImplies(
                        Ctx.MkNot(Ctx.MkEq(e1, e2)),
                        Ctx.MkGt(Cache.MkLen(e2), Ctx.MkInt(0))
                    )
                );
                var s = Cache.TryParseStr(e1);
                Debug.Assert(s is not null);
                AddNotEpsilonInternal(s);
                return;
            }

            if (
                Cache.ExprToStrToken.TryGetValue(e1, out var t1) && t1 is UnitToken c1 &&
                Cache.ExprToStrToken.TryGetValue(e2, out var t2) && t2 is UnitToken c2) {
                if (c1 is CharToken ch1 && c2 is CharToken ch2) {
                    if (!ch1.Equals(ch2))
                        return;
                    Debug.Assert(false); // Why would Z3 report this?!
                    Propagate([], Ctx.MkDistinct(e1, e2));
                    return;
                }
                AddCharDiseq(c1, c2);
                return;
            }

            StrVarToken x1 = GetFreshAuxStr();
            Expr x1e = x1.ToExpr(Graph);
            SymCharToken o1 = new();
            StrVarToken y1 = GetFreshAuxStr();

            StrVarToken x2 = GetFreshAuxStr();
            Expr x2e = x2.ToExpr(Graph);
            SymCharToken o2 = new();
            StrVarToken y2 = GetFreshAuxStr();

            Str u1 = [x1, o1, y1];
            Str u2 = [x2, o2, y2];

            Propagate([],
                Ctx.MkEq(
                    Ctx.MkNot(Ctx.MkEq(e1, e2)),
                    Ctx.MkOr(
                        Ctx.MkNot(Ctx.MkEq(Cache.MkLen(e1), Cache.MkLen(e2))),
                        Ctx.MkAnd(
                            Ctx.MkEq(e1, u1.ToExpr(Graph)),
                            Ctx.MkEq(e2, u2.ToExpr(Graph)),
                            Ctx.MkEq(Cache.MkLen(x1e), Cache.MkLen(x2e)),
                            Ctx.MkNot(Ctx.MkEq(o1.ToExpr(Graph), o2.ToExpr(Graph)))
                        )
                    )
                )
            );
        }
        catch (Exception ex) {
            Console.WriteLine("Exception (DisEq): " + ex.Message);
        }
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
}

public sealed class SaturatingStringPropagator : StringPropagator {

    public bool Cancel { get; set; }

    public override NielsenGraph Graph { get; }
    public NielsenNode Root { get; } // This node is added as cloned to the graph - we can alter the constraints in it

    List<(Expr lhs, Expr rhs)> reportedEqs = [];
    List<BoolExpr> reportedFixed = [];

    readonly HashSet<BoolExpr> forbidden = [];
    HashSet<BoolExpr>? selectedPath;
    bool newInformation;

    public SaturatingStringPropagator(Solver solver, ExpressionCache cache) : base(solver, cache) {
        Graph = new NielsenGraph(this);
        Root = new NielsenNode(Graph);
        Final = FinalCB;
        Decide = DecideCB;
    }

    protected override void GotNegContains(BoolExpr e) {
        reportedFixed.Add((BoolExpr)e.Dup());
        undoStack.Add(() => reportedFixed.Pop());
        // TODO
        throw new NotImplementedException("!contains");
    }

    protected override void GotPathLiteral(BoolExpr e, bool val) {
        if (val) {
            if (selectedPath is null)
                return;
            // Just chose another unassigned path literal
            foreach (var path in selectedPath) {
                if (NextSplit(path, 0, 1))
                    break;
            }
            return;
        }
        if (selectedPath is not null && selectedPath.Contains(e)) {
            var prev = selectedPath;
            selectedPath = null;
            undoStack.Add(() => selectedPath = prev);
        }

        var e2 = (BoolExpr)e.Dup();
        var s = forbidden.Add(e2);
        Debug.Assert(s);
        undoStack.Add(() => forbidden.Remove(e2));

    }

    protected override void AddCharDiseqInternal(DisEq disEq) {
        if (!Root.AddDisEq(disEq))
            return;
        if (!newInformation) {
            newInformation = true;
            undoStack.Add(() => newInformation = false);
        }
        undoStack.Add(() => Root.RemoveDisEq(disEq));
    }

    public override void EqInternal(Str s1, Expr e1, Str s2, Expr e2) {

        var eq = new StrEq(s1, s2);
        NonTermSet nonTermSet = new();
        HashSet<CharToken> alph = [];
        eq.CollectSymbols(nonTermSet, alph);

        if (Root.StrEq.Add(eq)) { // u = v
            undoStack.Add(() =>
            {
                Log.Verify(Root.StrEq.Remove(eq));
            });
            if (!newInformation) {
                newInformation = true;
                undoStack.Add(() => newInformation = false);
            }
        }
        var la = new IntEq(LenVar.MkLenPoly(s1), LenVar.MkLenPoly(s2));
        if (!la.Poly.IsZero && Root.IntEq.Add(la)) { // u = v => |u| = |v|
            undoStack.Add(() =>
            {
                Log.Verify(Root.IntEq.Remove(la));
            });
            if (!newInformation) {
                newInformation = true;
                undoStack.Add(() => newInformation = false);
            }
        }
        // foreach (var a in alph) {
        //     if (Root.IntEq.Add(new IntEq(Parikh.MkParikhPoly(a, s1), Parikh.MkParikhPoly(a, s2)))) // u = v => |u|_a = |v|_a
        //         undoStack.Add(Root.IntEq.Pop);
        // }
        reportedEqs.Add((e1, e2));
        undoStack.Add(() =>
        {
            reportedEqs.Pop();
        });
    }

    protected override void AddNotEpsilonInternal(Str s) {
        var c = IntLe.MkLt(new IntPoly(), LenVar.MkLenPoly(s));
        if (!Root.IntLe.Add(c)) 
            return;
        undoStack.Add(() =>
        { 
            Log.Verify(Root.IntLe.Remove(c));
        });
    }

    int finalCnt;

    void FinalCB() {
        try {
            if (!newInformation && selectedPath is not null && selectedPath.All(o => !forbidden.Contains(o)))
                // We made our choice and the solver did not backtrack it/contradict it - we silently agree
                return;
            finalCnt++;
            Log.WriteLine("Final (" + finalCnt + ")");

            // used to get the set of blocked edges responsible for unsat (not all fixed path literals might be relevant)
            HashSet<BoolExpr> usedForbidden = [];
            var res = Graph.Check(Root, forbidden, usedForbidden);
            if (newInformation) {
                newInformation = false;
                undoStack.Add(() => newInformation = true);
            }
            // For now, we just add all the reported equations/fixed literals and the relevant blockings
            EqualityPairs pair = new();
            foreach (var (lhs, rhs) in reportedEqs) {
                pair.Add(lhs, rhs);
            }
            if (res) {
                var prev = selectedPath;
                selectedPath = new HashSet<BoolExpr>();
                bool madeGuess = false;
                foreach (var path in Graph.CurrentPath) {
                    foreach (BoolExpr c in path.Asserted) {
                        Propagate([], c);
                    }
                    selectedPath.Add(path.Assumption);
                    Register(path.Assumption);
                    if (!madeGuess)
                        madeGuess = NextSplit(path.Assumption, 0, 1);
                }
                undoStack.Add(() => selectedPath = prev);
            }
            else {
                var f = new BoolExpr[usedForbidden.Count + reportedFixed.Count];
                usedForbidden.CopyTo(f, 0);
                reportedFixed.CopyTo(f, usedForbidden.Count);
                Propagate(f, pair, Ctx.MkFalse());
            }
        }
        catch (SolverTimeoutException) {
        }
        catch (Exception ex) {
            Console.WriteLine("Exception (Final): " + ex.Message);
        }
    }

    void DecideCB(Expr term, uint idx, bool phase) {
        if (!phase && term.NumArgs == 0) 
            // Path literals are better true
            NextSplit(term, 0, 1);

    }

    public bool GetModel(out Interpretation itp) {

        Debug.Assert(Graph.CurrentRoot is not null);
        var currentRoot = Graph.CurrentRoot!;
        var currentPath = Graph.CurrentPath.ToList();
        var satNode = currentPath.IsEmpty() ? currentRoot : currentPath[^1].Tgt;
        Debug.Assert(satNode.StrEq.Count == 0);
        
        Graph.ResetIndices(); // We need the original indices for retrieving the correct root constraints

        NonTermSet initNonTermSet = new();
        HashSet<CharToken> initAlphabet = [];
        currentRoot.CollectSymbols(initNonTermSet, initAlphabet);

        foreach (Constraint c in currentRoot.AllConstraints.Where(o => o is not StrEq)) {
            BoolExpr e = c.ToExpr(Graph);
            Solver.Assert(e);
        }
        foreach (var diseq in currentRoot.DisEqs) {
            // TODO: Optimize via distinct
            Expr e = diseq.Key.ToExpr(Graph);
            foreach (UnitToken d in diseq.Value) {
                Solver.Assert(Ctx.MkDistinct(e, d.ToExpr(Graph)));
            }
        }
        // TODO: Do this also in other places
        foreach (var path in currentPath) {
            foreach (BoolExpr c in path.Asserted) {
                Solver.Assert(c);
            }
            Solver.Assert(path.Assumption);
        }

        var res = Solver.Check();
        Debug.Assert(res == Status.SATISFIABLE);
        var model = Solver.Model;

        itp = new Interpretation();
        foreach (var c in model.Consts) {
            if (c.Key.Apply() is not IntExpr i)
                continue;
            if (!Cache.ExprToIntToken.TryGetValue(i, out var vt) || vt is not IntVar v)
                continue;
            itp.Add(v, ((IntNum)c.Value).BigInteger);
            if (!satNode.ConsistentIntVal(v, ((IntNum)c.Value).BigInteger))
                Console.WriteLine("Z3 Model is not consistent with internal bounds on " + v);
        }
        Debug.Assert(model is not null);

        for (int i = 0; i < currentPath.Count; i++) {
            foreach (var subst in currentPath[^(i + 1)].Subst) {
                subst.AddToInterpretation(itp);
            }
        }

        if (Options.ModelCompletion)
            itp.Complete(initAlphabet);

        bool modelCheck = true;
        var allConstraints = currentRoot.AllConstraints.Select(o => o.Clone());
        foreach (var cnstr in allConstraints) {
            var orig = cnstr.Clone();
            cnstr.Apply(itp);
            BacktrackReasons reason = BacktrackReasons.Unevaluated;
            if (cnstr.SimplifyAndPropagate(satNode, new NonTermSet(), new DetModifier(), ref reason, true) == SimplifyResult.Satisfied)
                continue;
            modelCheck = false;
            Console.WriteLine("Constraint " + orig + " not satisfied: " + cnstr);
        }

        Console.WriteLine(modelCheck ? "Model seems fine" : "ERROR: Created invalid model");

        itp.ProjectTo(initNonTermSet);

        return modelCheck;
    }
}

public class LemmaStringPropagator : StringPropagator {

    public override NielsenGraph Graph { get; }

    public LemmaStringPropagator(Solver solver, ExpressionCache cache, NielsenGraph graph) : base(solver, cache) {
        Graph = graph;
    }
}