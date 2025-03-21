using System.Diagnostics;
using System.Diagnostics.CodeAnalysis;
using System.Reflection;
using System.Text;
using Microsoft.Z3;
using StringBreaker.Constraints;
using StringBreaker.Constraints.ConstraintElement;
using StringBreaker.IntUtils;
using StringBreaker.Tokens;

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

        ulong timeout = 0;
        if (args.Length > 1) {
            if (!ulong.TryParse(args[1], out timeout))
                Usage();
        }

        // Global.SetParameter("proof", "true");
        // Global.SetParameter("smt.up.persist_clauses", "false");

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
            if (Solve(propagator, timeout) is SolveResult.SAT or SolveResult.UNSAT)
                solved++;
            GC.Collect(0);
        }
        Console.WriteLine("Solved: " + solved + " / " + total);
    }

    static SolveResult Solve(OuterStringPropagator propagator, ulong timeout) {
        Global.SetParameter("smt.random_seed", "16");
        Global.SetParameter("nlsat.randomize", "false");
        Global.SetParameter("nlsat.seed", "10");
        Global.SetParameter("smt.arith.random_initial_value", "false");
        if (timeout > 0)
            Console.WriteLine("Timeout: " + timeout + "s");
        if (timeout != 0)
            Global.SetParameter("timeout", (timeout * 1000).ToString());
        var res = propagator.Solver.Check();
        Console.WriteLine("Depth Bound: " + propagator.Graph.DepthBound);
        Console.WriteLine("Complexity Bound: " + propagator.Graph.ComplexityBound);
#if DEBUG
        // Console.WriteLine(propagator.Graph.ToDot());
#endif
        if (res == Status.SATISFIABLE) {
            if (Options.GetAndCheckModel) {
                Console.WriteLine("SAT:");
                bool succ = propagator.GetModel(out var itp);
                Console.WriteLine(itp);
                propagator.Solver.Pop(propagator.Solver.NumScopes);
                return succ ? SolveResult.SAT : SolveResult.UNSOUND;
            }
            Console.WriteLine("SAT");
            propagator.Solver.Pop(propagator.Solver.NumScopes);
            return SolveResult.SAT;
        }
        if (res == Status.UNSATISFIABLE) {
            Console.WriteLine("UNSAT");
            // Console.WriteLine(solver.Proof);
            return SolveResult.UNSAT;
        }
        Console.WriteLine("UNKNOWN");
        return SolveResult.UNKNOWN;
    }

    static void AssertSMTLIB(Context ctx, Solver solver, OuterStringPropagator propagator, string path) {
        string content = File.ReadAllText(path);
        BoolExpr[]? exprs = ctx.ParseSMTLIB2String(content);
        foreach (var expr in exprs) {
            var cnstr = propagator.TryParse(expr);
            solver.Assert(cnstr.ToExpr(propagator.Graph));
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
        using OuterStringPropagator propagator = new(solver);
        solver.Assert(eq.ToExpr(propagator.Graph));
        Solve(propagator, 0);
    }
}