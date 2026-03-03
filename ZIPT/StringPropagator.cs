using Microsoft.Z3;
using System.Diagnostics;
using System.Numerics;
using System.Xml.Linq;
using ZIPT.Constraints;
using ZIPT.Constraints.ConstraintElement;
using ZIPT.Constraints.ConstraintElement.AuxConstraints;
using ZIPT.Constraints.Modifier;
using ZIPT.IntUtils;
using ZIPT.MiscUtils;
using ZIPT.Strings;
using ZIPT.Strings.Chunks;
using ZIPT.Strings.Tokens;
using ZIPT.Strings.Tokens.RegexTokens;

namespace ZIPT;

// Base user-propagator integrating the Nielsen search with Z3's UP interface.
// Responsible for translating Z3 string terms to internal `Str` representation,
// reacting to created/fixed/equality/disequality callbacks, and emitting propagation
// lemmas that drive the Nielsen search.
public abstract class StringPropagator : UserPropagator {

    public readonly Context Ctx;
    public readonly Solver Solver;
    public readonly Environment Env;

    public abstract NielsenGraph Graph { get; }

    protected readonly UndoStack undoStack = new();

    protected StringPropagator(Solver solver, Environment env) : base(solver) {
        Solver = solver;
        Ctx = solver.Context;
        Env = env;

        Fixed = FixedCB;
        Created = CreatedCB;
        Eq = EqCB;
        Diseq = DisEqCB;
    }

    StrVarToken GetFreshAuxStr() => 
        Env.CreateFreshStrVar("x");

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

    // Callback invoked when a (user-propagator) term becomes fixed to true/false.
    // This emits immediate structural consequences (e.g., decompositions for prefix/suffix/contains)
    // which the SMT solver can use to prune the search.
    void FixedCB(Expr e, Expr valExpr) {
        try {
            Debug.Assert(valExpr.IsTrue || valExpr.IsFalse);
            fixedCnt++;
            bool val = valExpr.IsTrue;

            var f = e.FuncDecl;
            if (Env.IsPrefixOf(f)) {
                
                Expr u = e.Arg(0);
                Expr v = e.Arg(1);
                Expr x = GetFreshAuxStr().ToExpr(Env, []);

                if (val) {
                    // e := prefixOf(u, v)
                    // e |- v = ux
                    Propagate([e], Ctx.MkEq(v, Env.MkConcat(u, x)));
                    return;
                }
                // e :=: !prefixOf(u, v)
                // e |- |u| > |v| || (v = xy && |x| = |u| && x != u)
                IntExpr lenU = Env.MkLen(u);
                IntExpr lenV = Env.MkLen(v);
                Expr y = GetFreshAuxStr().ToExpr(Env, []);
                Propagate([e],
                    Ctx.MkOr(
                        Ctx.MkGt(lenU, lenV),
                        Ctx.MkAnd(
                            Ctx.MkEq(v, Env.MkConcat(x, y)),
                            Ctx.MkEq(Env.MkLen(x), Env.MkLen(u)),
                            Ctx.MkNot(Ctx.MkEq(u, x))
                        )
                    )
                );
                return;
            }
            if (Env.IsSuffixOf(f)) {

                Expr u = e.Arg(0);
                Expr v = e.Arg(1);
                Expr x = GetFreshAuxStr().ToExpr(Env, []);

                if (val) {
                    // e := suffixOf(u, v)
                    // e |- v = xu
                    Propagate([e], Ctx.MkEq(v, Env.MkConcat(x, u)));
                    return;
                }
                // e :=: !suffixOf(u, v)
                // e |- |u| > |v| || (v = yx && |x| = |u| && x != u)
                IntExpr lenU = Env.MkLen(u);
                IntExpr lenV = Env.MkLen(v);
                Expr y = GetFreshAuxStr().ToExpr(Env, []);
                Propagate([e],
                    Ctx.MkOr(
                        Ctx.MkGt(lenU, lenV),
                        Ctx.MkAnd(
                            Ctx.MkEq(v, Env.MkConcat(y, x)),
                            Ctx.MkEq(Env.MkLen(x), Env.MkLen(u)),
                            Ctx.MkNot(Ctx.MkEq(u, x))
                        )
                    )
                );
                return;
            }
            if (Env.IsContains(f)) {
                if (!val) {
                    GotNegContains((BoolExpr)e);
                    return;
                }
                // e := contains(u, v)
                // e |- |v| = 0 || u = xvy (the first case only to speed up)
                Expr u = e.Arg(0);
                Expr v = e.Arg(1);
                IntExpr lenV = Env.MkLen(v);
                Expr x = GetFreshAuxStr().ToExpr(Env, []);
                Expr y = GetFreshAuxStr().ToExpr(Env, []);
                Propagate([e],
                    Ctx.MkOr(
                        Ctx.MkEq(lenV, Ctx.MkInt(0)),
                        Ctx.MkEq(u, Env.MkConcat(x, Env.MkConcat(v, y)))
                    )
                );
                return;
            }
            if (Env.IsRegularMembership(f)) {
                // In theory, we could now assert the semi-linear length set, but not sure if this is too costly
                Expr e1 = e.Arg(0);
                Expr e2 = e.Arg(1);
                var s1 = Env.TryParseStr(e1);
                var s2 = Env.TryParseStr(e2);
                Debug.Assert(s1 is not null);
                Debug.Assert(s2 is not null);
                if (!val)
                    s2 = Env.StrManager.MkComplement(s2);
                MemInternal(s1, s2, (BoolExpr)e);
                return;
            }

            GotPathLiteral((BoolExpr)e, val);
        }
        catch (Exception ex) {
            Console.WriteLine("Exception (Fixed): " + ex.Message);
        }
    }

    // Callback invoked when a new term is created under the UP translation. Used to
    // rewrite complicated functions (strAt, subStr, indexOf, len, ...) into lemmas.
    void CreatedCB(Expr e) {

        // Just rewrite complicated function symbols
        if (e.Sort is not BoolSort && !e.Sort.Equals(Env.StringSort) && e.Sort is not IntSort)
            return;

        var f = e.FuncDecl;

        if (Env.IsStrAt(f)) {
            // e := strAt(u, i)
            // (i < 0 || i >= |u|) => |e| = 0
            // !(i < 0 || i >= |u|) => (|e| = 1 && u = xey && |x| = i)
            Expr u = e.Arg(0);
            IntExpr i = (IntExpr)e.Arg(1);
            IntExpr lenU = Env.MkLen(u);
            IntExpr lenE = Env.MkLen(e);
            IntExpr zero = Ctx.MkInt(0);
            IntExpr one = Ctx.MkInt(1);
            BoolExpr outsideBounds = Ctx.MkOr(
                Ctx.MkLt(i, Ctx.MkInt(0)),
                Ctx.MkGe(i, lenU)
            );
            Expr x = GetFreshAuxStr().ToExpr(Env, []);
            Expr y = GetFreshAuxStr().ToExpr(Env, []);
            IntExpr lenX = Env.MkLen(x);
            Propagate([], Ctx.MkImplies(outsideBounds, Ctx.MkEq(lenE, zero)));
            Propagate([],
                Ctx.MkImplies(Ctx.MkNot(outsideBounds),
                    Ctx.MkAnd(
                        Ctx.MkEq(lenE, one),
                        Ctx.MkEq(lenX, i),
                        Ctx.MkEq(u, Env.MkConcat(x, Env.MkConcat(e, y)))
                    )
                )
            );
            return;
        }
        if (Env.IsSubstring(f)) {
            // e := subStr(u, from, len)
            // (from < 0 || len <= 0 || from >= |u|) => |e| = 0
            // (from >= 0 && len > 0 && from < |u| && from + len >= |u|) =>
            //      (u = xe && |x| = from && |e| = |u| - from)
            // (from >= 0 && len > 0 && from + len < |u|) =>
            //      (u = xey && |x| = from && |e| = len)
            Expr u = e.Arg(0);
            IntExpr from = (IntExpr)e.Arg(1);
            IntExpr len = (IntExpr)e.Arg(2);
            IntExpr lenU = Env.MkLen(u);
            IntExpr lenE = Env.MkLen(e);
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
            Expr x = GetFreshAuxStr().ToExpr(Env, []);
            Expr y = GetFreshAuxStr().ToExpr(Env, []);
            IntExpr lenX = Env.MkLen(x);
            Propagate([],
                Ctx.MkImplies(
                    Ctx.MkAnd(
                        Ctx.MkGe(from, zero),
                        Ctx.MkGt(len, zero),
                        Ctx.MkLt(from, lenU),
                        Ctx.MkGe(Ctx.MkAdd(from, len), lenU)
                    ),
                    Ctx.MkAnd(
                        Ctx.MkEq(u, Env.MkConcat(x, e)),
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
                        Ctx.MkEq(u, Env.MkConcat(x, Env.MkConcat(e, y))),
                        Ctx.MkEq(lenX, from),
                        Ctx.MkEq(lenE, len)
                    )
                )
            );
            return;
        }
        if (Env.IsIndexOf(f)) {
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
            IntExpr lenU = Env.MkLen(u);
            IntExpr lenV = Env.MkLen(v);
            IntExpr zero = Ctx.MkInt(0);
            IntExpr negOne = Ctx.MkInt(-1);
            Expr x = GetFreshAuxStr().ToExpr(Env, []);
            Expr y = GetFreshAuxStr().ToExpr(Env, []);
            IntExpr lenX = Env.MkLen(x);
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
                    Ctx.MkNot((BoolExpr)Env.ContainsFct.Apply(u, v)),
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
                        Ctx.MkEq(u, Env.MkConcat(x, Env.MkConcat(v, y))),
                        Ctx.MkEq(lenX, from),
                        Ctx.MkNot(
                            (BoolExpr)Env.ContainsFct.Apply(
                                Env.SubstringFct.Apply(Env.MkConcat(x, v), zero, Ctx.MkAdd(lenX, lenV, negOne)), v)
                        )
                    )
                )
            );
            return;
        }
        if (Env.IsLen(f)) {
            Expr arg0 = e.Arg(0);
            FuncDecl f0 = arg0.FuncDecl;
            if (Env.IsConcat(f0)) {
                Stack<Expr> args = [];
                args.Push(arg0);
                IntExpr sum = Ctx.MkInt(0);
                while (args.IsNonEmpty()) {
                    var arg = args.Pop();
                    if (Env.IsConcat(arg.FuncDecl)) {
                        args.Push(arg.Arg(0));
                        args.Push(arg.Arg(1));
                        continue;
                    }
                    sum = (IntExpr)Ctx.MkAdd(sum, Env.MkLen(arg));
                }
                Propagate([], Ctx.MkEq(e, sum));
                return;
            }
            if (f0.Equals(Env.Epsilon.FuncDecl)) {
                Propagate([], Ctx.MkEq(e, Ctx.MkInt(0)));
                return;
            }
            if (Env.IsPower(f0)) {
                Propagate([], Ctx.MkEq(e, Ctx.MkMul(Env.MkLen(arg0.Arg(0)), (IntExpr)arg0.Arg(1))));
                return;
            }
            if (Env.ExprToStrToken.TryGetValue(arg0, out var s)) {
                if (s is UnitToken) {
                    Propagate([], Ctx.MkEq(e, Ctx.MkInt(1)));
                    return;
                }
                Debug.Assert(s is NamedStrToken);
                var lenTerm = new LenVar((NamedStrToken)s).ToExpr(Env, []);
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
        //         while (args.NonEmpty) {
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

    public virtual void EqInternal(Str s1, Expr e1, Str s2, Expr e2) {}
    public virtual void MemInternal(Str s1, Str s2, BoolExpr e) {}

    static int eqCount;

    // Callback for equalities between translated string expressions. Collects
    // pairs and delegates to `EqInternal` for solver-specific handling.
    void EqCB(Expr e1, Expr e2) {
        try {
            if (e1.Equals(e2))
                return;

            if (!e1.Sort.Equals(Env.StringSort))
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

            var s1 = Env.TryParseStr(e1);
            var s2 = Env.TryParseStr(e2);
            Debug.Assert(s1 is not null);
            Debug.Assert(s2 is not null);

            if (s1.Length >= 2 && s2.Length >= 2) {
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
                modRaw.Add(cnt1);
                uint cnt2 = (uint)s2.Count(o => o is NonTermToken v2 && v2.Equals(v));
                modRaw.Add(cnt2);
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
                        mod.Add((uint)i);
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
                        mod.Add(i);
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

            EqInternal(s1, e1, s2, e2);
        }
        catch (Exception ex) {
            Console.WriteLine("Exception (Eq): " + ex.Message);
        }
    }

    protected virtual void AddNotEpsilonInternal(Expr s) {}

    // Callback for disequalities between translated string expressions. Emits
    // structural disjunctions that witness inequality (length differences or differing chars).
    void DisEqCB(Expr e1, Expr e2) {
        try {
            if (!e1.Sort.Equals(Env.StringSort))
                return;
            // TODO: Fix for characters. e.g., o1 != o2 clauses infinite recursion!

            if (Env.Epsilon.Equals(e2))
                (e1, e2) = (e2, e1);

            if (Env.Epsilon.Equals(e1)) {
                if (Env.ExprToStrToken.TryGetValue(e2, out var t) && t is UnitToken) {
                    Propagate([], Ctx.MkDistinct(e1, e2));
                    return;
                }
                Propagate([],
                    Ctx.MkImplies(
                        Ctx.MkNot(Ctx.MkEq(e1, e2)),
                        Ctx.MkGt(Env.MkLen(e2), Ctx.MkInt(0))
                    )
                );
                AddNotEpsilonInternal(e1);
                return;
            }

            if (
                Env.ExprToStrToken.TryGetValue(e1, out var t1) && t1 is CharToken c1 &&
                Env.ExprToStrToken.TryGetValue(e2, out var t2) && t2 is CharToken c2) {
                if (!c1.Equals(c2))
                    return;
                Debug.Assert(false); // Why would Z3 report this?!
                Propagate([], Ctx.MkDistinct(e1, e2));
                return;
            }

            StrVarToken x1 = GetFreshAuxStr();
            Expr x1e = x1.ToExpr(Env, []);
            StrVarToken o1 = GetFreshAuxStr();
            StrVarToken y1 = GetFreshAuxStr();

            StrVarToken x2 = GetFreshAuxStr();
            Expr x2e = x2.ToExpr(Env, []);
            StrVarToken o2 = GetFreshAuxStr();
            StrVarToken y2 = GetFreshAuxStr();

            Str u1 = Env.MkString(x1, o1, y1);
            Str u2 = Env.MkString(x2, o2, y2);

            Propagate([],
                Ctx.MkEq(
                    Ctx.MkNot(Ctx.MkEq(e1, e2)),
                    Ctx.MkOr(
                        Ctx.MkNot(Ctx.MkEq(Env.MkLen(e1), Env.MkLen(e2))),
                        Ctx.MkAnd(
                            Ctx.MkEq(e1, u1.ToExpr(Env, [])),
                            Ctx.MkEq(e2, u2.ToExpr(Env, [])),
                            Ctx.MkEq(Env.MkLen(x1e), Env.MkLen(x2e)),
                            Ctx.MkEq(Env.MkLen(o1.ToExpr(Env)), Ctx.MkInt(1)),
                            Ctx.MkEq(Env.MkLen(o2.ToExpr(Env)), Ctx.MkInt(1)),
                            Ctx.MkNot(Ctx.MkEq(o1.ToExpr(Env), o2.ToExpr(Env)))
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
    // Implementation of the string propagator that drives a full Nielsen search.
    // Collects equation/membership facts from Z3, builds the root Nielsen node and
    // runs the search to produce propagation lemmas or a model.
    public bool Cancel { get; set; }

    public override NielsenGraph Graph { get; }
    public LocalInfo? Info { get; set; }

    List<(Str s1, Str s2, Expr e1, Expr e2)> reportedEqs = [];
    List<Str> reportedNonEmpty = [];
    List<(Str s1, Str s2, BoolExpr e)> reportedMems = [];
    List<BoolExpr> reportedFixed = [];

    readonly HashSet<BoolExpr> forbidden = [];
    HashSet<BoolExpr>? selectedPath;
    bool newInformation;

    public SaturatingStringPropagator(Solver solver, Environment env) : base(solver, env) {
        Graph = new NielsenGraph(this);
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

    public override void EqInternal(Str s1, Expr e1, Str s2, Expr e2) {

        if (!newInformation) {
            newInformation = true;
            undoStack.Add(() => newInformation = false);
        }
        reportedEqs.Add((s1, s2, e1.Dup(), e2.Dup()));
        undoStack.Add(() =>
        {
            reportedEqs.Pop();
        });
    }

    public override void MemInternal(Str s1, Str s2, BoolExpr e) {

        reportedMems.Add((s1, s2, (BoolExpr)e.Dup()));
        undoStack.Add(() =>
        {
            reportedMems.Pop();
        });
        if (!newInformation) {
            newInformation = true;
            undoStack.Add(() => newInformation = false);
        }
    }

    protected override void AddNotEpsilonInternal(Expr s) {
        var parsed = Env.TryParseStr(s);
        if (parsed is null)
            return;
        reportedNonEmpty.Add(parsed);
        undoStack.Add(() => reportedNonEmpty.Pop());
        if (!newInformation) {
            newInformation = true;
            undoStack.Add(() => newInformation = false);
        }
    }

    int finalCnt;

    // Final callback invoked by Z3 when the current set of assertions is stable.
    // Builds the search root from collected facts, runs the Nielsen graph check and
    // emits blocking lemmas or model-based propagations accordingly.
    void FinalCB() {
        try {
            if (!newInformation && selectedPath is not null && selectedPath.All(o => !forbidden.Contains(o)) && !Info.OutdatedModel)
                // We made our choice and the solver did not backtrack it/contradict it - we silently agree
                return;
            finalCnt++;
            Log.WriteLine("Final (" + finalCnt + ")");

            // Create the root node and populate it directly from pre-parsed constraints
            var root = new NielsenNode(Graph);
            int constraintCnt = reportedEqs.Count + reportedNonEmpty.Count + reportedMems.Count;
            Dictionary<NamedStrToken, Str> units = [];
            int id = 0;
            for (int i = 0; i < reportedEqs.Count; i++) {
                var (s1, s2, _, _) = reportedEqs[i];
                var dep = new DependencyTracker(constraintCnt, id++);
                root.ConstraintsStrEq.Add(new StrEq(s1, s2, dep));
                if (s1.Length == 1 && s1[0] is StrVarToken x1 && s2.Ground)
                    units.Add(x1, s2);
                else if (s2.Length == 1 && s2[0] is StrVarToken x2 && s1.Ground)
                    units.Add(x2, s1);

                var la = new IntEq(LenVar.MkLenPoly(s1, Env), LenVar.MkLenPoly(s2, Env), dep);
                if (!la.Poly.IsZero)
                    root.ConstraintsIntEq.Add(la);
            }
            for (int i = 0; i < reportedNonEmpty.Count; i++) {
                var s = reportedNonEmpty[i];
                var c = IntLe.MkLt(Env.ZeroInt, LenVar.MkLenPoly(s, Env), new DependencyTracker(constraintCnt, id++));
                root.ConstraintsIntLe.Add(c);
            }
            for (int i = 0; i < reportedMems.Count; i++) {
                // Unfortunately Z3 might rewrite some constant strings within the membership constraints to variables...
                // We rewrite it to the constant
                var (s1, s2, _) = reportedMems[i];
                foreach (var x in s2.ContainedVars()) {
                    Debug.Assert(units.ContainsKey(x));
                    s2 = Env.StrManager.Subst(s2, x, units[x]);
                }
                root.ConstraintsStrMem.Add((uint)i, new StrMem(s1, s2, Env.EmptyStr, (uint)i, new DependencyTracker(constraintCnt, id++)));
            }

            // used to get the set of blocked edges responsible for unsat (not all fixed path literals might be relevant)
            Info = new LocalInfo(root, forbidden);
            var res = Graph.Check(Info);
            if (newInformation) {
                newInformation = false;
                undoStack.Add(() => newInformation = true);
            }
            // For now, we just add all the reported equations/fixed literals and the relevant blockings
            EqualityPairs pair = new();
            foreach (var (_, _, e1, e2) in reportedEqs) {
                pair.Add(e1, e2);
            }
            if (res) {
                var prev = selectedPath;
                selectedPath = [];
                bool madeGuess = false;
                foreach (var path in Info.CurrentPath) {
                    foreach (var r in path.Value.Asserted) {
                        selectedPath.Add(r);
                        Register(r);
                        if (!madeGuess)
                            madeGuess = NextSplit(r, 0, 1);
                    }
                }
                undoStack.Add(() => selectedPath = prev);
            }
            else {
                var memExprs = reportedMems.Select(m => m.e).ToArray();
                var f = new BoolExpr[Info.UsedForbidden.Count + memExprs.Length + reportedFixed.Count];
                Info.UsedForbidden.CopyTo(f, 0);
                memExprs.CopyTo(f, Info.UsedForbidden.Count);
                reportedFixed.CopyTo(f, Info.UsedForbidden.Count + memExprs.Length);
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
        if (!phase && selectedPath is not null && selectedPath.Contains(term)) 
            // Path literals are better true
            NextSplit(term, 0, 1);
    }

    // Extract a concrete Interpretation (model) from a completed successful Nielsen search.
    public bool GetModel(LocalInfo info, out Interpretation itp) {

        Debug.Assert(!info.OutdatedModel);
        var currentPath = info.CurrentPath.ToList();
        var satNode = currentPath.Count == 0 ? info.RootNode : currentPath[^1].Value.Tgt;
        Debug.Assert(satNode is not null);
        Debug.Assert(satNode.ConstraintsStrEq.Count == 0);
        Debug.Assert(satNode.ConstraintsStrMem.All(o => o.Value.IsPrimitiveRegex()));
        
        NonTermSet initNonTermSet = new();
        CharacterSet initAlphabet = new CharacterSet();
        info.RootNode.CollectSymbols(initNonTermSet, initAlphabet);

        using var checkSolver = Ctx.MkSimpleSolver();

        foreach (Constraint c in info.RootNode.AllConstraints.Where(o => o.Shared)) {
            BoolExpr e = c.ToExpr(info);
            checkSolver.Assert(e);
        }
        info.DelayedAssert(checkSolver, info.RootNode.Id);

        var res = checkSolver.Check();
        Debug.Assert(res == Status.SATISFIABLE);
        var model = checkSolver.Model;

        itp = new Interpretation(Env);
        foreach (var c in model.Consts) {
            Expr @const = c.Key.Apply();
            if (@const is not IntExpr i)
                continue;
            if (!Env.ExprToIntToken.TryGetValue(i, out var vt) || vt is not IntVar v)
                continue;
            itp.Add(v, ((IntNum)c.Value).BigInteger);
            if (!satNode.ConsistentIntVal(v, ((IntNum)c.Value).BigInteger))
                Console.WriteLine("Z3 Model is not consistent with internal bounds on " + v);
        }
        Debug.Assert(model is not null);

        var witnesses = satNode.WitnessRegex();
        foreach (var (nt, v) in witnesses) {
            new Subst(nt, Env.MkString(v.OfType<StrToken>().ToList())).AddToInterpretation(itp);
        }

        for (int i = 0; i < currentPath.Count; i++) {
            foreach (var subst in currentPath[^(i + 1)].Value.Subst) {
                subst.AddToInterpretation(itp);
            }
            foreach (var subst in currentPath[^(i + 1)].Value.SubstC) {
                subst.AddToInterpretation(itp);
            }
        }

        if (Options.ModelCompletion)
            itp.Complete(/*initAlphabet, */model, info);
        itp.Simplify();

        bool modelCheck = true;

        if (Options.CheckModel) {
            List<(Constraint orig, Constraint simpl)> failed = info.RootNode.CheckModel(itp);
            foreach (var fail in failed) {
                Console.WriteLine("Constraint " + fail.orig + " not satisfied: " + fail.simpl);
            }
            modelCheck = failed.Count == 0;

            Console.WriteLine(modelCheck ? "Model seems fine" : "ERROR: Created invalid model");
        }

        itp.ProjectTo(initNonTermSet);
        return modelCheck;
    }
}

public class LemmaStringPropagator : StringPropagator {
    // Lightweight propagator variant that wraps an existing NielsenGraph. Used when
    // the outer solver only needs lemma-generation support without full saturation.
    public override NielsenGraph Graph { get; }

    public LemmaStringPropagator(Solver solver, Environment env, NielsenGraph graph) : base(solver, env) => 
        Graph = graph;
}