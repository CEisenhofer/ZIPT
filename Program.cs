using System.Diagnostics;
using System.Diagnostics.CodeAnalysis;
using System.Reflection;
using System.Text;
using Microsoft.Z3;
using StringBreaker.Constraints;
using StringBreaker.Constraints.ConstraintElement;
using StringBreaker.IntUtils;
using StringBreaker.MiscUtils;
using StringBreaker.Strings.Tokens;

namespace StringBreaker;

public enum SolveResult {
    SAT,
    UNSAT,
    UNKNOWN,
    UNSOUND
}

public static class Program {

    [DoesNotReturn]
    static void Usage() {
        Console.Error.WriteLine("Usage: " + Assembly.GetExecutingAssembly().Location + " <input> [timeout]");
        Environment.Exit(-1);
    }

    public static void Main(string[] args) {
        
        Console.OutputEncoding = Encoding.UTF8;

        Options.ModelCompletion = true;
        Options.ReasoningUnwindingBound = 1;
        Options.ModelUnwindingBound = 9;
        Options.ItDeepeningInc = 1;
        Options.ItDeepComplexityStart = 5;
        Options.ItDeepDepthStart = 5;
        Options.GetAndCheckModel = true;
        // Options.FullGraphExpansion = true;

        if (args.Length == 0) {
            Console.WriteLine("Test");
            Test();
            return;
        }

        if (!(args.Length is >= 1 and <= 2))
            Usage();

        if (!File.Exists(args[0]) && !Directory.Exists(args[0]))
            Usage();

        int timeout = 0;
        if (args.Length > 1) {
            if (!int.TryParse(args[1], out timeout) || timeout < 0)
                Usage();
        }

        // Global.SetParameter("proof", "true");
        Global.SetParameter("smt.up.persist_clauses", "false");

        if (File.Exists(args[0])) {
            Console.WriteLine(args[0]);
            using Context ctx = new();
            using Solver solver = ctx.MkSimpleSolver();
            using ExpressionCache cache = new(ctx);
            using SaturatingStringPropagator propagator = new(solver, cache);
            try {
                AssertSMTLIB(ctx, solver, propagator, args[0]);
            }
            catch (NotSupportedException ex) {
                Console.WriteLine("Unsupported feature: " + ex.Message);
                return;
            }
            Solve(propagator, timeout);
            return;
        }
        int solved = 0;
        int total = 0;
        foreach (var file in Directory.EnumerateFiles(args[0], "*.smt2", SearchOption.AllDirectories)) {
            Console.WriteLine(file);
            using Context ctx = new();
            using Solver solver = ctx.MkSimpleSolver();
            using ExpressionCache cache = new(ctx);
            using SaturatingStringPropagator propagator = new(solver, cache);
            total++;
            try {
                AssertSMTLIB(ctx, solver, propagator, file);
                if (Solve(propagator, timeout) is SolveResult.SAT or SolveResult.UNSAT)
                    solved++;
                else 
                    Console.WriteLine("Failed on " + file);
                GC.Collect(0);
            }
            catch (NotSupportedException ex) {
                Console.WriteLine("Unsupported feature: " + ex.Message);
            }
        }
        Console.WriteLine("Solved: " + solved + " / " + total);
    }

    static SolveResult Solve(SaturatingStringPropagator propagator, int timeout) {
        SolveResult result = SolveResult.UNKNOWN;
        Thread thread = new(() =>
        {
            Global.SetParameter("smt.random_seed", "16");
            Global.SetParameter("nlsat.randomize", "false");
            Global.SetParameter("nlsat.seed", "10");
            Global.SetParameter("smt.arith.random_initial_value", "false");
            if (timeout > 0)
                Console.WriteLine("Timeout: " + timeout + "s");
            if (timeout != 0)
                Global.SetParameter("timeout", ((ulong)timeout * 1000).ToString());
            SymCharToken.ResetCounter();
            var res = propagator.Solver.Check();
            Console.WriteLine("Depth Bound: " + propagator.Graph.DepthBound);
            Console.WriteLine("Complexity Bound: " + propagator.Graph.ComplexityBound);
#if DEBUG
            // Console.WriteLine(propagator.Graph.ToDot());
#endif
            if (res == Status.SATISFIABLE && propagator.Graph.SatNodes.IsNonEmpty()) {
                Console.WriteLine("SAT");
                if (Options.GetAndCheckModel) {
                    bool succ = propagator.GetModel(out var itp);
                    Console.WriteLine(itp);
                    propagator.Solver.Pop(propagator.Solver.NumScopes);
                    result = succ ? SolveResult.SAT : SolveResult.UNSOUND;
                    return;
                }
                propagator.Solver.Pop(propagator.Solver.NumScopes);
                result = SolveResult.SAT;
                return;
            }
            if (res == Status.UNSATISFIABLE) {
                Console.WriteLine("UNSAT");
                // Console.WriteLine(solver.Proof);
                result = SolveResult.UNSAT;
                return;
            }
            Console.WriteLine("UNKNOWN");
            result = SolveResult.UNKNOWN;
        });
        thread.Start();
        if (timeout > 0)
            thread.Join(timeout * 1000);
        else
            thread.Join();
        if (thread.IsAlive) {
            propagator.Cancel = true;
            thread.Join();
            propagator.Cancel = false;
        }
        return result;
    }

    static void AssertSMTLIB(Context ctx, Solver solver, StringPropagator propagator, string path) {
        string content = File.ReadAllText(path);
        BoolExpr[]? exprs = ctx.ParseSMTLIB2String(content);
        foreach (var expr in exprs) {
            var cnstr = propagator.Cache.TryParse(expr);
            if (cnstr is null)
                throw new NotSupportedException(expr.ToString());
            solver.Assert(cnstr.ToExpr());
        }
    }

    static void Test() {
        StrEq eq = new(
            [
                new CharToken('a'),
                new PowerToken(
                [
                    new CharToken('b'),
                    new CharToken('c'),
                    new CharToken('a')
                ], new Poly(new IntVar())),
                new CharToken('b'),
                new CharToken('c')
            ],
            [
                new PowerToken(
                [
                    new CharToken('a'),
                    new CharToken('b'),
                    new CharToken('c')
                ], new Poly(new IntVar())),
            ]
        );
        using Context ctx = new();
        using Solver solver = ctx.MkSimpleSolver();
        using ExpressionCache cache = new(ctx);
        using SaturatingStringPropagator propagator = new(solver, cache);
        solver.Assert(eq.ToExpr());
        Solve(propagator, 0);
    }
}