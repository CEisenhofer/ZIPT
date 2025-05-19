using System.Diagnostics;
using System.Diagnostics.CodeAnalysis;
using System.Reflection;
using System.Text;
using Microsoft.Z3;
using ZIPT.Constraints;
using ZIPT.MiscUtils;
using ZIPT.Constraints.ConstraintElement;
using ZIPT.IntUtils;
using ZIPT.Tokens;

namespace ZIPT;

public enum SolveResult {
    SAT,
    UNSAT,
    UNKNOWN,
    UNSOUND
}

public static class Program {

    [DoesNotReturn]
    static void Usage(string error) {
        Console.Error.WriteLine(error);
        Console.Error.WriteLine("Usage: " + Assembly.GetExecutingAssembly().Location + " [timeout] <input>");
        Environment.Exit(-1);
    }

    public static void Main(string[] args) {
        
        Console.OutputEncoding = Encoding.UTF8;

        Options.ModelCompletion = true;
        Options.ReasoningUnwindingBound = 1;
        Options.ModelUnwindingBound = 9;
        Options.ItDeepeningInc = 1;
        Options.ItDeepDepthStart = 1;
        Options.GetAndCheckModel = true;
        // Options.FullGraphExpansion = true;

        if (!(args.Length is >= 1 and <= 2))
            Usage("Expected 1-2 arguments. Got: " + args.Length);

        if (!File.Exists(args[^1]) && !Directory.Exists(args[^1]))
            Usage("Could not find file " + args[^1]);

        int timeout = 0;
        if (args.Length > 1) {
            if (!int.TryParse(args[0], out timeout) || timeout < 0)
                Usage("Could not parse integer " + args[0]);
        }

        // Global.SetParameter("proof", "true");
        Global.SetParameter("smt.up.persist_clauses", "false");

        if (File.Exists(args[^1])) {
            Console.WriteLine(args[^1]);
            using Context ctx = new();
            using Solver solver = ctx.MkSimpleSolver();
            using ExpressionCache cache = new(ctx);
            using SaturatingStringPropagator propagator = new(solver, cache);
            try {
                AssertSMTLIB(ctx, solver, propagator, args[^1]);
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
        foreach (var file in Directory.EnumerateFiles(args[^1], "*.smt2", SearchOption.AllDirectories)) {
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
                Console.WriteLine("Timeout: " + timeout + "ms");
            if (timeout != 0)
                Global.SetParameter("timeout", ((ulong)timeout).ToString());
            SymCharToken.ResetCounter();
            var res = propagator.Solver.Check();
            Console.WriteLine("Depth Bound: " + propagator.Graph.DepthBound);
#if DEBUG
            // Console.WriteLine(propagator.Graph.ToDot());
#endif
            if (!propagator.Cancel) {
                if (res == Status.SATISFIABLE) {
                    Console.WriteLine("SAT");
                    if (Options.GetAndCheckModel) {
                        bool success = propagator.GetModel(out var itp);
                        Console.WriteLine(itp);
                        propagator.Solver.Pop(propagator.Solver.NumScopes);
                        result = success ? SolveResult.SAT : SolveResult.UNSOUND;
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
            }
            Console.WriteLine("UNKNOWN");
            result = SolveResult.UNKNOWN;
        });
        thread.Start();
        if (timeout > 0)
            thread.Join(timeout);
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
            solver.Assert((BoolExpr)(propagator.Cache.TranslateStr(expr, propagator.Graph) ?? expr));
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
                ], new IntPoly(new IntVar())),
                new CharToken('b'),
                new CharToken('c')
            ],
            [
                new PowerToken(
                [
                    new CharToken('a'),
                    new CharToken('b'),
                    new CharToken('c')
                ], new IntPoly(new IntVar())),
            ]
        );
        using Context ctx = new();
        using Solver solver = ctx.MkSimpleSolver();
        using ExpressionCache cache = new(ctx);
        using SaturatingStringPropagator propagator = new(solver, cache);
        solver.Assert(eq.ToExpr(propagator.Graph));
        Solve(propagator, 0);
    }
}