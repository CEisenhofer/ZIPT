using Microsoft.Z3;
using System.Diagnostics;
using System.Diagnostics.CodeAnalysis;
using System.Reflection;
using System.Text;
using ZIPT.Constraints;

namespace ZIPT;

public enum SolveResult {
    SAT,
    UNSAT,
    CYCLIC,
    UNKNOWN,
    UNSOUND,
}

public static class ZiptSolver {

    [DoesNotReturn]
    static void Usage(string? error) {
        if (error is not null)
            Console.Error.WriteLine(error);
        Console.Error.WriteLine("Usage: " + Assembly.GetExecutingAssembly().Location + " [Arguments] <input>");
        Console.Error.WriteLine("Arguments:");
        Console.Error.WriteLine("\t-t:<timeout>   Set the time-out in milliseconds. Default: 0 (no timeout)");
        Console.Error.WriteLine("\t-e:<encoding>  Sets the character encoding [ascii, bmp, utf]");
        Console.Error.WriteLine("\t-c             Complete Model");
        Console.Error.WriteLine("\t-m             Output Model");
        Console.Error.WriteLine("\t-p             Retain proof graph. (one graph for each string solver call)");
        Console.Error.WriteLine("\t-g             Output Nielsen Graph");
        Console.Error.WriteLine("\t-v             Validate Model");
        Console.Error.WriteLine("\t-h             Show this help message");
        System.Environment.Exit(-1);
    }

    public static void ParseOptions(string[] args) {
        Debug.Assert(args.Length > 0);
        for (int i = 0; i < args.Length - 1; i++) {
            string arg = args[i];
            if (arg.StartsWith("-t:")) {
                if (!int.TryParse(arg[3..], out int timeout) || timeout < 0)
                    Usage("Could not parse timeout " + args[0]);
                Options.TimeOut = timeout;
                continue;
            }
            if (arg.StartsWith("-e:")) {
                string name = arg[3..];
                switch (name.ToLower()) {
                    case "ascii":
                        Options.MaxChar = Options.MaxCharAscii;
                        break;
                    case "bmp":
                        Options.MaxChar = Options.MaxCharBmp;
                        break;
                    case "utf":
                    case "unicode":
                        Options.MaxChar = Options.MaxCharUtf;
                        break;
                    default:
                        Usage("Unknown character encoding: " + name);
                        return;
                }
                continue;
            }
            if (arg == "-p") {
                Options.KeepProof = true;
                continue;
            }
            if (arg == "-c") {
                Options.ModelCompletion = true;
                continue;
            }
            if (arg == "-v") {
                Options.CheckModel = true;
                continue;
            }
            if (arg == "-a") {
                Options.SaturateGraph = true;
                continue;
            }
            if (arg == "-m") {
                Options.OutputModel = true;
                continue;
            }
            if (arg == "-s") {
                Options.OutputStats = true;
                continue;
            }
            if (arg == "-g") {
                Options.KeepProof = true;
                Options.OutputGraph = true;
                continue;
            }
            if (arg is "-h" or "-help") {
                Usage(null);
                return;
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
        ThreadStart run = () =>
        {
            Global.SetParameter("smt.random_seed", "16");
            Global.SetParameter("nlsat.randomize", "false");
            Global.SetParameter("nlsat.seed", "10");
            Global.SetParameter("smt.arith.random_initial_value", "false");
            if (Options.TimeOut > 0)
                Console.WriteLine("Timeout: " + Options.TimeOut + "ms");
            if (Options.TimeOut != 0)
                Global.SetParameter("timeout", ((ulong)Options.TimeOut).ToString());
            var res = propagator.Solver.Check();
            // Console.WriteLine("Depth Bound: " + propagator.Graph.DepthBound);
#if DEBUG
            // Console.WriteLine(propagator.Graph.ToDot());
#endif
            if (Options.OutputStats)
                OutputStats();
            if (!propagator.Cancel) {
                if (res == Status.SATISFIABLE) {
                    Console.WriteLine("SAT");
                    if (Options.OutputModel || Options.CheckModel) {
                        if (Options.SaturateGraph) {
                            try {
                                Options.SaturateGraph = false;
                                bool s = propagator.Graph.Check(propagator.Info!);
                                Debug.Assert(s);
                            }
                            finally {
                                Options.SaturateGraph = true;
                            }
                        }
                        bool success = propagator.GetModel(propagator.Info!, out var itp);
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
        };
        if (Options.TimeOut > 0) {
            Thread thread = new(run);
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
        }
        else
            run();
        return result;
    }

    static void OutputStats() {
        var properties = typeof(Stats).GetProperties();
        List<(string name, int value)> entries = [];
        foreach (var property in properties) {
            var attribute = (StatAttribute?)Attribute.GetCustomAttribute(property, typeof(StatAttribute));
            if (attribute is null)
                continue;
            var getter = property.GetMethod;
            if (getter is null || getter.ReturnType != typeof(int))
                continue;
            object? val = getter.Invoke(null, []);
            if (val is null || val.GetType() != typeof(int))
                continue;
            entries.Add((attribute.Name, (int)val));
        }
        int maxLen = entries.Max(o => o.name.Length);
        Console.WriteLine("Stats:");
        foreach (var entry in entries) {
            int padding = maxLen - entry.name.Length;
            string s = entry.name + ": " + new string(' ', padding) + entry.value;
            Console.WriteLine(s);
        }
    }

    static void AssertSMTLIB(Context ctx, Solver solver, SaturatingStringPropagator propagator, string path) {
        string content = File.ReadAllText(path);
        BoolExpr[]? exprs = ctx.ParseSMTLIB2String(content);
        foreach (var expr in exprs) {
            solver.Assert((BoolExpr)(propagator.Env.TranslateStr(expr, propagator.Info) ?? expr));
        }
    }
}