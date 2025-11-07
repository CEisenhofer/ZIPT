using Microsoft.Z3;
using ZIPT;
using ZIPT.Constraints.ConstraintElement;
using ZIPT.Strings.Chunks;
using ZIPT.Strings.Tokens;
using ZIPT.Strings.Tokens.RegexTokens;
using Environment = ZIPT.Environment;

namespace Test;

public static class Test {

    const bool IsCheckStrEquations = true;
    const bool IsCheckStrMembership = true;
    const bool IsCheckParikh = true;

    static void Main(string[] _) {
        Console.WriteLine("Starting Tests");
        Global.SetParameter("smt.string_solver", "none");
        Options.KeepProof = true;
        Options.ModelCompletion = true;
        Options.CheckModel = true;
        CheckStrEquations();
        CheckStrMembership();
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
        bool res = propagator.Graph.Check(root, [], []);
        if (res)
            propagator.GetModel(out _);
        return res;
    }

    static bool CheckMembership(Environment env, string s, Str regex) => 
        CheckMembership(env, new StrMem(ParseStr(s, env), regex));

    static bool CheckMembership(Environment env, params StrMem[] cnstrs) {
        Console.WriteLine($"Checking memberships {string.Join(" & ", cnstrs.Select(o => o.Str + " in " + o.Regex))}");
        using Solver solver = env.Ctx.MkSimpleSolver();
        using SaturatingStringPropagator propagator = new(solver, env);
        var root = propagator.Root;
        foreach (var cnstr in cnstrs) {
            root.AddConstraint(cnstr);
        }
        bool res = propagator.Graph.Check(root, [], []);
        if (res)
            propagator.GetModel(out _);
        return res;
    }

    static void EqSAT(string lhs, string rhs) {
        if (CheckEquation(lhs, rhs))
            return;
        Console.WriteLine($"Expected SAT on \"{lhs}\" = \"{rhs}\" but got UNSAT");
        System.Environment.Exit(-1);
    }

    static void EqUNSAT(string lhs, string rhs) {
        if (!CheckEquation(lhs, rhs))
            return;
        Console.WriteLine($"Expected UNSAT on \"{lhs}\" = \"{rhs}\" but got SAT");
        System.Environment.Exit(-1);
    }

    static void MemSAT(Environment env, params StrMem[] cnstrs) {
        if (CheckMembership(env, cnstrs))
            return;
        Console.WriteLine($"Expected SAT on {string.Join(" & ", cnstrs.Select(o => o.Str + " in " + o.Regex))} but got UNSAT");
        System.Environment.Exit(-1);
    }

    static void MemUNSAT(Environment env, params StrMem[] cnstrs) {
        if (!CheckMembership(env, cnstrs))
            return;
        Console.WriteLine($"Expected UNSAT on {string.Join(" & ", cnstrs.Select(o => o.Str + " in " + o.Regex))} but got SAT");
        System.Environment.Exit(-1);
    }

    static void MemSAT(Environment env, string str, Str regex) {
        if (CheckMembership(env, str, regex))
            return;
        Console.WriteLine($"Expected SAT on \"{str}\" in \"{regex}\" but got UNSAT");
        System.Environment.Exit(-1);
    }

    static void MemUNSAT(Environment env, string str, Str regex) {
        if (!CheckMembership(env, str, regex))
            return;
        Console.WriteLine($"Expected UNSAT on \"{str}\" in \"{regex}\" but got SAT");
        System.Environment.Exit(-1);
    }

    static void CheckStrEquations() {
        if (!IsCheckStrEquations)
            return;
        Console.WriteLine("Checking String Equation...");
        EqSAT("aX", "YX");
        EqSAT("aX", "Xa");
        EqUNSAT("aX", "Xb");
        EqSAT("abX", "Xba");
        EqSAT("XabY", "YbaX");
        EqUNSAT("abcX", "Xbac");
        EqUNSAT("aaX", "Xa");
        // UNSAT("XaY", "YbX");
        EqUNSAT("aa", "XXX");
        EqSAT("abab", "XX");
        EqSAT("aX", "XY");
    }

    static void CheckStrMembership() {
        if (!IsCheckStrMembership)
            return;
        Console.WriteLine("Checking String Membership...");
        using Context ctx = new();
        using Environment env = new Environment(ctx);


        MemUNSAT(env, "XabX",
            // (aba)*
            env.MkString(new KleeneToken(ParseStr("aba", env)))
        );

        MemSAT(env, "aX",
            // a(a)*
            env.MkString(new CharToken('a'), new KleeneToken(ParseStr("a", env)))
        );
        MemUNSAT(env,
            // x \in (aa)*a && x \in (aa)*
            new StrMem(ParseStr("X", env),
                env.StrManager.Concat(
                    env.StrManager.MkStar(ParseStr("aa", env)), ParseStr("a", env))
            ),
            new StrMem(ParseStr("X", env),
                env.StrManager.MkStar(ParseStr("aa", env))
            )
        );
        MemSAT(env,
            // x \in (aa)*aa && x \in (aa)*
            new StrMem(ParseStr("X", env),
                env.StrManager.Concat(
                    env.StrManager.MkStar(ParseStr("aa", env)), ParseStr("aa", env))
            ),
            new StrMem(ParseStr("X", env), env.StrManager.MkStar(ParseStr("aa", env)))
        );
        MemSAT(env, "Xa",
            // a(a)*
            env.StrManager.Concat(ParseStr("a", env), env.StrManager.MkStar(ParseStr("a", env)))
        );
        MemSAT(env, "Xa",
            // a(a)*a
            env.StrManager.Concat(ParseStr("a", env), 
                env.StrManager.Concat(env.StrManager.MkStar(ParseStr("a", env)), ParseStr("a", env)))
        );
        MemUNSAT(env, "bX",
            // a(a)*
            env.MkString(new KleeneToken(ParseStr("a", env)), new CharToken('a'))
        );
        MemUNSAT(env, "bX",
            // (a)*
            env.MkString(new KleeneToken(ParseStr("a", env)))
        );
        MemUNSAT(env, "bX",
            // (a)*a
            env.MkString(new KleeneToken(ParseStr("a", env)), new CharToken('a'))
        );
        MemSAT(env, "bX",
            // (b)*a
            env.MkString(new KleeneToken(ParseStr("b", env)), new CharToken('a'))
        );
        MemSAT(env, "bXb",
            // (b)*a(b)*
            env.MkString(new KleeneToken(ParseStr("b", env)), new CharToken('a'), new KleeneToken(ParseStr("b", env)))
        );
        MemSAT(env, "bXbb",
            // (b)*a(b)*
            env.MkString(new KleeneToken(ParseStr("b", env)), new CharToken('a'), new KleeneToken(ParseStr("b", env)))
        );
        MemSAT(env, "XX",
            // a(a)*
            env.MkString(new CharToken('a'), new KleeneToken(ParseStr("a", env)))
        );
        MemSAT(env, "XaX",
            // aa(a)*
            env.MkString(new CharToken('a'), new CharToken('a'), new KleeneToken(ParseStr("a", env)))
        );
        MemSAT(env, "XX",
            // aaa(a)*
            env.MkString(new CharToken('a'), new CharToken('a'), new CharToken('a'), new KleeneToken(ParseStr("a", env)))
        );
        MemUNSAT(env, "XbX",
            // (a)*
            env.MkString(new KleeneToken(ParseStr("a", env)))
        );
        MemSAT(env, "XbX",
            // (a)*(b)*
            env.MkString(new KleeneToken(ParseStr("a", env)), new KleeneToken(ParseStr("b", env)))
        );
        MemSAT(env, "XbX",
            // (a)*(b)*(a)*a
            env.MkString(new KleeneToken(ParseStr("a", env)), new KleeneToken(ParseStr("b", env)), new KleeneToken(ParseStr("a", env)), new CharToken('a'))
        );



        MemUNSAT(env, "XaX",
            // (ab)*
            env.MkString(new KleeneToken(ParseStr("ab", env)))
        );
        MemSAT(env, "X",
            // a|b
            env.StrManager.MkUnion([
                ParseStr("a", env),
                ParseStr("b", env),
            ])
        );
        MemUNSAT(env, "XX",
            // a|b
            env.StrManager.MkUnion([
                ParseStr("a", env),
                ParseStr("b", env),
            ])
        );
        MemUNSAT(env, "XX",
            // (ab)|(ba)
            env.StrManager.MkUnion([
                ParseStr("ab", env),
                ParseStr("ba", env),
            ])
        );
        MemSAT(env, "XX",
            // ((ab)|(ba))((ba)|(ab))
            env.StrManager.Concat(
                env.StrManager.MkUnion([
                    ParseStr("ab", env),
                    ParseStr("ba", env),
                ]),
                env.StrManager.MkUnion([
                    ParseStr("ba", env),
                    ParseStr("ab", env),
                ])
            )
        );
        MemUNSAT(env, "XX",
            // ((ab)|(ba))((aa)|(bb))
            env.StrManager.Concat(
                env.StrManager.MkUnion([
                    ParseStr("ab", env),
                    ParseStr("ba", env),
                ]),
                env.StrManager.MkUnion([
                    ParseStr("aa", env),
                    ParseStr("bb", env),
                ])
            )
        );
        MemUNSAT(env, "bXbX",
            // (a)*(b)*(a)*a
            env.MkString(new KleeneToken(ParseStr("a", env)), new KleeneToken(ParseStr("b", env)), new KleeneToken(ParseStr("a", env)), new CharToken('a'))
        );
        MemSAT(env, "XdX",
            // (a|b)*da(a|c)*
            env.MkString(
                new KleeneToken(env.StrManager.Single(new UnionToken(ParseStr("a", env), ParseStr("b", env)))),
                new CharToken('d'),
                new CharToken('a'),
                new KleeneToken(env.StrManager.Single(new UnionToken(ParseStr("a", env), ParseStr("c", env))))
            )
        );
        // These require more sophisticated splittings
        MemUNSAT(env,
            // xabx \in (ab)*
            // xbabx \in a(ba)*
            [
                new StrMem(
                    ParseStr("XabX", env),
                    env.StrManager.Single(new KleeneToken(ParseStr("ab", env)))
                ),
                new StrMem(
                    ParseStr("XbabX", env),
                    env.MkString(
                        new CharToken('a'),
                        new KleeneToken(ParseStr("ba", env))
                    )
                ),
            ]
        );
        MemUNSAT(env, "XX",
            // (aba)*a
            env.MkString(new KleeneToken(ParseStr("aba", env)), new CharToken('a'))
        );
        MemUNSAT(env, "XaX",
            // (aa)*
            env.StrManager.Single(new KleeneToken(ParseStr("aa", env)))
        );
        MemUNSAT(env, "XX",
            // (ab)*a
            env.MkString(new KleeneToken(ParseStr("ab", env)), new CharToken('a'))
        );
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