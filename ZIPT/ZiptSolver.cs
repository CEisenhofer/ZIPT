using System.Diagnostics;
using System.Diagnostics.CodeAnalysis;
using System.Reflection;
using System.Text;
using Microsoft.Z3;
using ZIPT.Tokens;

namespace ZIPT;

public enum SolveResult {
    SAT,
    UNSAT,
    UNKNOWN,
    UNSOUND
}

public static class ZiptSolver {

    [DoesNotReturn]
    static void Usage(string? error) {
        if (error is not null)
            Console.Error.WriteLine(error);
        Console.Error.WriteLine("Usage: " + Assembly.GetExecutingAssembly().Location + " [Arguments] <input>");
        Console.Error.WriteLine("Arguments:");
        Console.Error.WriteLine("\t-t:<timeout>   Set the time-out in milliseconds. Default: 0 (no timeout).");
        Console.Error.WriteLine("\t-c             Complete Model.");
        Console.Error.WriteLine("\t-m             Output Model.");
        Console.Error.WriteLine("\t-p             Retain proof graph. (one graph for each string solver call)");
        Console.Error.WriteLine("\t-g             Output Nielsen Graph.");
        Console.Error.WriteLine("\t-v             Validate Model.");
        Console.Error.WriteLine("\t-h             Show this help message.");
        System.Environment.Exit(-1);
    }

    public static void ParseOptions(string[] args) {
        Debug.Assert(args.Length > 0);
        for (int i = 1; i < args.Length - 1; i++) {
            string arg = args[i];
            if (arg.StartsWith("-t:")) {
                if (!int.TryParse(arg[3..], out int timeout) || timeout < 0)
                    Usage("Could not parse timeout " + args[0]);
                Options.TimeOut = timeout;
                continue;
            }
            if (arg.StartsWith("-p")) {
                Options.KeepProof = true;
                continue;
            }
            if (arg.StartsWith("-c")) {
                Options.ModelCompletion = true;
                continue;
            }
            if (arg.StartsWith("-v")) {
                Options.CheckModel = true;
                continue;
            }
            if (args[i].StartsWith("-m")) {
                Options.OutputModel = true;
                continue;
            }
            if (args[i].StartsWith("-g")) {
                Options.KeepProof = true;
                Options.OutputGraph = true;
                continue;
            }
            if (arg.StartsWith("-h")) {
                Usage(null);
            }
        }
    }

    public static void Main(string[] args) {
        
        Console.OutputEncoding = Encoding.UTF8;

        Options.ReasoningUnwindingBound = 1;
        Options.ModelUnwindingBound = 9;
        Options.ItDeepeningInc = 1;
        Options.ItDeepDepthStart = 1;
        Options.TimeOut = 0;
#if DEBUG
        Options.KeepProof = true;
        Options.OutputModel = true;
        Options.CheckModel = true;
#endif

        ParseOptions(args);

        if (args.Length < 2) {
            Usage("Not input file given");
        }

        if (!File.Exists(args[^1]) && !Directory.Exists(args[^1]))
            Usage("Could not find file " + args[^1]);

        // Global.SetParameter("proof", "true");
        Global.SetParameter("smt.up.persist_clauses", "false");

        if (File.Exists(args[^1])) {
            Console.WriteLine(args[^1]);
            using Context ctx = new();
            using Solver solver = ctx.MkSimpleSolver();
            using Environment cache = new(ctx);
            using SaturatingStringPropagator propagator = new(solver, cache);
            try {
                AssertSMTLIB(ctx, solver, propagator, args[^1]);
            }
            catch (NotSupportedException ex) {
                Console.WriteLine("Unsupported feature: " + ex.Message);
                return;
            }
            Solve(propagator);
            return;
        }
        int solved = 0;
        int total = 0;
        foreach (var file in Directory.EnumerateFiles(args[^1], "*.smt2", SearchOption.AllDirectories)) {
            Console.WriteLine(file);
            using Context ctx = new();
            using Solver solver = ctx.MkSimpleSolver();
            using Environment cache = new(ctx);
            using SaturatingStringPropagator propagator = new(solver, cache);
            total++;
            try {
                AssertSMTLIB(ctx, solver, propagator, file);
                if (Solve(propagator) is SolveResult.SAT or SolveResult.UNSAT)
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

    public static SolveResult Solve(SaturatingStringPropagator propagator) {
        SolveResult result = SolveResult.UNKNOWN;
        Thread thread = new(() =>
        {
            Global.SetParameter("smt.random_seed", "16");
            Global.SetParameter("nlsat.randomize", "false");
            Global.SetParameter("nlsat.seed", "10");
            Global.SetParameter("smt.arith.random_initial_value", "false");
            if (Options.TimeOut > 0)
                Console.WriteLine("Timeout: " + Options.TimeOut + "ms");
            if (Options.TimeOut != 0)
                Global.SetParameter("timeout", ((ulong)Options.TimeOut).ToString());
            SymCharToken.ResetCounter();
            var res = propagator.Solver.Check();
            // Console.WriteLine("Depth Bound: " + propagator.Graph.DepthBound);
#if DEBUG
            // Console.WriteLine(propagator.Graph.ToDot());
#endif
            if (!propagator.Cancel) {
                if (res == Status.SATISFIABLE) {
                    Console.WriteLine("SAT");
                    if (Options.OutputModel || Options.CheckModel) {
                        bool success = propagator.GetModel(out var itp);
                        if (Options.OutputModel)
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
        if (Options.TimeOut > 0)
            thread.Join(Options.TimeOut);
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
            solver.Assert((BoolExpr)(propagator.Env.TranslateStr(expr, propagator.Graph) ?? expr));
        }
    }
}