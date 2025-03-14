using System.Diagnostics;
using System.Reflection;
using System.Text;
using Microsoft.Z3;
using StringBreaker.Constraints;
using StringBreaker.Constraints.ConstraintElement;
using StringBreaker.Tokens;

namespace StringBreaker;

public static class Program {

    public static void Main(string[] args) {
        if ((args.Length != 1 && args.Length != 2) || (!File.Exists(args[0]) && !Directory.Exists(args[0]))) {
            Console.Error.WriteLine("Usage: " + Assembly.GetExecutingAssembly().Location + " <input> [timeout]");
            return;
        }

        Console.OutputEncoding = Encoding.UTF8;

        ulong timeout = 0;
        if (args.Length > 1) {
            if (!ulong.TryParse(args[1], out timeout)) {
                Console.Error.WriteLine("Usage: " + Assembly.GetExecutingAssembly().Location + " <input> [timeout]");
                return;
            }
        }

        // Global.SetParameter("proof", "true");
        Global.SetParameter("smt.up.persist_clauses", "false");

        if (File.Exists(args[0])) {
            Console.WriteLine(args[0]);
            using Context ctx = new();
            using Solver solver = ctx.MkSimpleSolver();
            using OuterStringPropagator propagator = new(solver);
            AssertSMTLIB(ctx, solver, propagator, args[0]);
            Solve(propagator, timeout);
            return;
        }
        int solved = 0;
        int total = 0;
        foreach (var file in Directory.EnumerateFiles(args[0], "*.smt2", SearchOption.AllDirectories)) {
            Console.WriteLine(file);
            using Context ctx = new();
            using Solver solver = ctx.MkSimpleSolver();
            using OuterStringPropagator propagator = new(solver);
            AssertSMTLIB(ctx, solver, propagator, file);
            total++;
            if (Solve(propagator, timeout))
                solved++;
            GC.Collect(0);
        }
        Console.WriteLine("Solved: " + solved + " / " + total);
    }

    static bool Solve(OuterStringPropagator propagator, ulong timeout) {
        Global.SetParameter("smt.random_seed", "16");
        Global.SetParameter("nlsat.randomize", "false");
        Global.SetParameter("nlsat.seed", "10");
        Global.SetParameter("smt.arith.random_initial_value", "false");
        if (timeout > 0)
            Console.WriteLine("Timeout: " + timeout + "s");
        Global.SetParameter("timeout", (timeout * 1000).ToString());
        var res = propagator.Solver.Check();
        Console.WriteLine("Level: " + propagator.Graph.ComplexityBound);
#if DEBUG
        // Console.WriteLine(propagator.Graph.ToDot());
#endif
        if (res == Status.SATISFIABLE) {
            Console.WriteLine("SAT:");
            Console.WriteLine(propagator.GetModel());
            propagator.Solver.Pop(propagator.Solver.NumScopes);
        }
        else if (res == Status.UNSATISFIABLE) {
            Console.WriteLine("UNSAT");
            // Console.WriteLine(solver.Proof);
        }
        else {
            Console.WriteLine("UNKNOWN");
            return false;
        }
        return true;
    }

    static void AssertSMTLIB(Context ctx, Solver solver, OuterStringPropagator propagator, string path) {
        string content = File.ReadAllText(path);
        BoolExpr[]? exprs = ctx.ParseSMTLIB2String(content);
        foreach (var expr in exprs) {
            var cnstr = Parse(expr);
            solver.Assert(cnstr.ToExpr(propagator.Graph));
        }
    }

    static StrConstraint Parse(BoolExpr expr) {
        switch (expr.FuncDecl.DeclKind) {
            case Z3_decl_kind.Z3_OP_EQ:
                return ParseEq(expr.Args[0], expr.Args[1]);
            case Z3_decl_kind.Z3_OP_NOT:
                var cnstr = Parse((BoolExpr)expr.Args[0]);
                return cnstr.Negate();
            case Z3_decl_kind.Z3_OP_LT:
            case Z3_decl_kind.Z3_OP_GT:
            case Z3_decl_kind.Z3_OP_LE:
            case Z3_decl_kind.Z3_OP_GE:
                throw new NotImplementedException("Rewrite in terms of custom length function");
            default:
                throw new NotImplementedException();
        }
    }

    static StrEq ParseEq(Expr left, Expr right) => 
        new(ParseStr(left), ParseStr(right));

    static Str ParseStr(Expr expr) {
        Debug.Assert(expr.Sort is SeqSort);
        if (expr.IsString)
            return new Str(expr.String.Select(o => (StrToken)new CharToken(o)).ToArray());
        if (expr.IsConst)
            return new Str([StrVarToken.GetOrCreate(expr.FuncDecl.Name.ToString())]);
        if (expr.IsConcat)
            return new Str(expr.Args.SelectMany(ParseStr).ToArray());
        throw new NotSupportedException();
    }
}