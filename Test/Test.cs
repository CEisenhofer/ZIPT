using Microsoft.Z3;
using ZIPT;
using ZIPT.Constraints.ConstraintElement;
using ZIPT.Strings.Chunks;
using ZIPT.Strings.Tokens;
using Environment = ZIPT.Environment;

namespace Test;

public static class Test {

    const bool IsCheckStrEquations = true;
    const bool IsCheckParikh = true;

    static void Main(string[] _) {
        Console.WriteLine("Starting Tests");
        Options.KeepProof = true;
        CheckStrEquations();
        CheckParikh();
    }

    static Str ParseStr(string str, Environment env) {
        List<StrToken> ret = [];
        foreach (char c in str) {
            if (char.IsUpper(c))
                ret.Add(env.GetOrCreateStrVar(c.ToString()));
            else
                ret.Add(new CharToken(c));
        }
        return env.MkString(ret);
    }

    static bool CheckEquation(string lhs, string rhs) {
        Console.WriteLine($"Checking eq {lhs} = {rhs}");
        using Context ctx = new();
        using Solver solver = ctx.MkSimpleSolver();
        using Environment env = new(ctx);
        using SaturatingStringPropagator propagator = new(solver, env);
        var root = propagator.Root;
        root.AddConstraint(new StrEq(ParseStr(lhs, env), ParseStr(rhs, env)));
        return propagator.Graph.Check(root, [], []);
    }

    static void SAT(string lhs, string rhs) {
        if (CheckEquation(lhs, rhs))
            return;
        Console.WriteLine($"Expected SAT on \"{lhs}\" = \"{rhs}\" but got UNSAT");
        System.Environment.Exit(-1);
    }

    static void UNSAT(string lhs, string rhs) {
        if (!CheckEquation(lhs, rhs))
            return;
        Console.WriteLine($"Expected UNSAT on \"{lhs}\" = \"{rhs}\" but got SAT");
        System.Environment.Exit(-1);
    }

    static void CheckStrEquations() {
        if (!IsCheckStrEquations)
            return;
        Console.WriteLine("Checking String Equations...");
        SAT("aX", "Xa");
        UNSAT("aX", "Xb");
        SAT("abX", "Xba");
        SAT("XabY", "YbaX");
        UNSAT("abcX", "Xbac");
        UNSAT("aaX", "Xa");
        // UNSAT("XaY", "YbX");
        UNSAT("aa", "XXX");
        SAT("abab", "XX");
        SAT("aX", "XY");
        SAT("aX", "YX");
    }

    static void ParikhUNSAT(string lhs, string rhs) {
        Console.WriteLine($"Checking Parikh {lhs} = {rhs}");
        using Context ctx = new();
        using Solver solver = ctx.MkSimpleSolver();
        using Environment env = new(ctx);
        throw new NotImplementedException();
        //if (!StrEq.CheckMultiSequenceParikh(ParseStr(lhs, env), ParseStr(rhs, env)))
            return;
        Console.WriteLine($"Expected UNSAT (Parikh) on \"{lhs}\" = \"{rhs}\"");
        System.Environment.Exit(-1);
    }

    static void CheckParikh() {
        if (!IsCheckParikh)
            return;
        // Single characters are covered in the string solver only; only proper multi-sequence checks
        Console.WriteLine("Checking Parikh Images...");
        Dictionary<char, StrVarToken> s2v = new();
        ParikhUNSAT("abcX", "Xbac");
        s2v.Clear();
        ParikhUNSAT("XabcY", "YbacX");
        s2v.Clear();
        ParikhUNSAT("XXabcYY", "YYbacXX");
        s2v.Clear();
        ParikhUNSAT("XXacdYYb", "YYabcdXX");
        s2v.Clear();
        ParikhUNSAT("YaXaaabbbbYX", "XYababababXY");
    }
}