using System.ComponentModel;
using System.ComponentModel.DataAnnotations;
using System.Diagnostics;
using System.Numerics;
using System.Text;
using Microsoft.Z3;
using StringBreaker.Constraints;
using StringBreaker.Constraints.ConstraintElement;
using StringBreaker.IntUtils;
using StringBreaker.MiscUtils;
using StringBreaker.Tokens;

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

    public readonly Dictionary<StrToken, Expr> StrTokenToExpr = [];
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

    public Expr? GetCachedStrExpr(StrToken t) => StrTokenToExpr.GetValueOrDefault(t);
    public IntExpr? GetCachedIntExpr(IntVar t) => IntTokenToExpr.GetValueOrDefault(t);

    public void SetCachedExpr(StrToken t, Expr e) {
        StrTokenToExpr.Add(t, e);
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

    void FixedCB(Expr e, Expr v) {
        try {
            Debug.Assert(v.IsBool);
            fixedCnt++;

            Log.WriteLine($"Fixed ({fixedCnt}): {StrToken.ExprToStr(Graph, e)} = {v}");
            Console.WriteLine($"Unexpected and ignored: {StrToken.ExprToStr(Graph, e)} = {v}");
        }
        catch (Exception ex) {
            Console.WriteLine("Exception (Fixed): " + ex.Message);
        }
    }

    void CreatedCB(Expr e) { }

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
            HashSet<StrVarToken> vars = [];
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
        switch (expr.FuncDecl.DeclKind) {
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
            default:
                throw new NotImplementedException();
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

    public Str? TryParseStr(Expr expr) {
        if (expr.Sort.Equals(StringSort)) {
            // Custom Z3
            if (expr.Equals(Epsilon))
                return [];
            if (expr.FuncDecl.Equals(ConcatFct)) {
                List<StrToken> res = [];
                for (uint i = 0; i < expr.NumArgs; i++) {
                    if (TryParseStr(expr.Arg(i)) is not { } str)
                        return null;
                    res.AddRange(str);
                }
                return new Str(res);
            }
            if (expr.FuncDecl.Equals(PowerFct)) {
                Str? @base = TryParseStr(expr.Arg(0));
                if (@base is null)
                    return null;
                Poly? poly = TryParseInt((IntExpr)expr.Arg(1));
                Debug.Assert(poly is not null);
                return new Str([new PowerToken(@base, poly)]);
            }
            if (ExprToStrToken.TryGetValue(expr, out StrToken? s))
                return [s];
        }
        else if (expr.Sort is SeqSort) {
            // Native Z3
            if (expr.IsString)
                return new Str(expr.String.Select(o => (StrToken)new CharToken(o)).ToArray());
            if (expr.IsConst)
                return new Str([StrVarToken.GetOrCreate(expr.FuncDecl.Name.ToString())]);
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
        }
        throw new NotSupportedException();
    }

    public Poly? TryParseInt(IntExpr expr) {
        if (expr.Sort is not IntSort)
            return null;
        if (expr is IntNum num)
            return new Poly(num.BigInteger);
        if (expr.FuncDecl.Equals(LenFct)) {
            Str? str = TryParseStr(expr.Arg(0));
            return str is null ? null : LenVar.MkLenPoly(str);
        }
        if (InvParikInfo.TryGetValue(expr.FuncDecl, out var parikhInfo)) {
            var s = TryParseStr((IntExpr)expr.Arg(0));
            if (s is null)
                return null;
            if (parikhInfo.IsTotal)
                return Parikh.MkParikhPoly(parikhInfo.Info.Char, s);
            throw new NotImplementedException();
        }
        if (expr.FuncDecl.Equals(LenFct)) {
            Str? str = TryParseStr(expr.Arg(0));
            return str is null ? null : LenVar.MkLenPoly(str);
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
        throw new NotSupportedException();
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
        
        HashSet<StrVarToken> initSVars = [];
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