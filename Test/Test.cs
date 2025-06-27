using Microsoft.Z3;
using ZIPT;
using ZIPT.Constraints;
using ZIPT.Constraints.ConstraintElement;
using ZIPT.Tokens;
using Environment = ZIPT.Environment;

namespace Test;

public static class Test {

    const bool IsCheckStrEquations = true;
    const bool IsCheckParikh = true;

    static void Main(string[] args) {
        Console.WriteLine("Starting Tests");

        CheckStrEquations();
        CheckParikh();
    }

    static Str ParseStr(string str, Dictionary<char, StrVarToken> symToVar) {
        Str ret = [];
        foreach (char c in str) {
            if (char.IsUpper(c)) {
                if (!symToVar.TryGetValue(c, out var v)) {
                    v = StrVarToken.GetOrCreate(c.ToString());
                    symToVar.Add(c, v);
                }
                ret.Add(v);
            }
            else
                ret.Add(new CharToken(c));
        }
        return ret;
    }

    static bool CheckEquation(Str lhs, Str rhs) {
        Console.WriteLine($"Checking eq {lhs} = {rhs}");
        using Context ctx = new();
        using Solver solver = ctx.MkSimpleSolver();
        using Environment cache = new(ctx);
        using SaturatingStringPropagator propagator = new(solver, cache);
        var root = propagator.Root;
        root.AddConstraint(new StrEq(lhs, rhs));
        return propagator.Graph.Check(root, [], []);
    }

    static void SAT(Str lhs, Str rhs) {
        if (CheckEquation(lhs, rhs))
            return;
        Console.WriteLine($"Expected SAT on \"{lhs}\" = \"{rhs}\" but got UNSAT");
        System.Environment.Exit(-1);
    }

    static void UNSAT(Str lhs, Str rhs) {
        if (!CheckEquation(lhs, rhs))
            return;
        Console.WriteLine($"Expected UNSAT on \"{lhs}\" = \"{rhs}\" but got SAT");
        System.Environment.Exit(-1);
    }

    static void CheckStrEquations() {
        if (!IsCheckStrEquations)
            return;
        Console.WriteLine("Checking String Equations...");
        Dictionary<char, StrVarToken> s2v = new();
        SAT(ParseStr("aX", s2v), ParseStr("Xa", s2v));
        s2v.Clear();
        UNSAT(ParseStr("aX", s2v), ParseStr("Xb", s2v));
        s2v.Clear();
        SAT(ParseStr("abX", s2v), ParseStr("Xba", s2v));
        s2v.Clear();
        UNSAT(ParseStr("abcX", s2v), ParseStr("Xbac", s2v));
        s2v.Clear();
        UNSAT(ParseStr("aaX", s2v), ParseStr("Xa", s2v));
        s2v.Clear();
        UNSAT(ParseStr("XaY", s2v), ParseStr("YbX", s2v));
        s2v.Clear();
        SAT(ParseStr("XabY", s2v), ParseStr("YbaX", s2v));
        s2v.Clear();
        UNSAT(ParseStr("aa", s2v), ParseStr("XXX", s2v));
        s2v.Clear();
        SAT(ParseStr("abab", s2v), ParseStr("XX", s2v));
        s2v.Clear();
        SAT(ParseStr("aX", s2v), ParseStr("XY", s2v));
        s2v.Clear();
        SAT(ParseStr("aX", s2v), ParseStr("YX", s2v));
    }

    static void ParikhUNSAT(Str lhs, Str rhs) {
        Console.WriteLine($"Checking Parikh {lhs} = {rhs}");
        if (!StrEq.CheckMultiSequenceParikh(lhs, rhs))
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
        ParikhUNSAT(ParseStr("abcX", s2v), ParseStr("Xbac", s2v));
        s2v.Clear();
        ParikhUNSAT(ParseStr("XabcY", s2v), ParseStr("YbacX", s2v));
        s2v.Clear();
        ParikhUNSAT(ParseStr("XXabcYY", s2v), ParseStr("YYbacXX", s2v));
        s2v.Clear();
        ParikhUNSAT(ParseStr("XXacdYYb", s2v), ParseStr("YYabcdXX", s2v));
        s2v.Clear();
        ParikhUNSAT(ParseStr("YaXaaabbbbYX", s2v), ParseStr("XYababababXY", s2v));
    }
}