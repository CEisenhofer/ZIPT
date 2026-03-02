using System.Diagnostics;
using Microsoft.Z3;
using ZIPT;
using ZIPT.Constraints;
using ZIPT.Constraints.ConstraintElement;
using ZIPT.MiscUtils;
using ZIPT.Strings.Chunks;
using ZIPT.Strings.Tokens;
using Environment = ZIPT.Environment;

namespace Test;

public static class Test {

    const bool IsCheckStrEquations = true;
    const bool IsCheckRegexMatching = true;
    const bool IsCheckStrMembership = true;
    const bool IsCheckParikh = true;
    const bool IsCheckCharacterSets = true;

    static void Main(string[] _) {
        Console.WriteLine("Starting Tests");
        Global.SetParameter("smt.string_solver", "none");
        Options.KeepProof = true;
        Options.ModelCompletion = true;
        Options.CheckModel = true;
        switch (Options.MaxChar) {
            case Options.MaxCharAscii:
                Global.SetParameter("encoding", "ascii");
                break;
            case Options.MaxCharBmp:
                Global.SetParameter("encoding", "bmp");
                break;
            case Options.MaxCharUtf:
                Global.SetParameter("encoding", "unicode");
                break;
            default:
                Debug.Assert(false);
                break;
        }
        CheckCharacterSets();
        CheckRegexMatching();
        CheckStrMembership();
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

    public static Str ParseRegex(string input, Environment env) {
        Debug.Assert(!input.Contains(' '));
        if (input is null)
            throw new ArgumentNullException(nameof(input));

        int pos = 0;
        int len = input.Length;

        Str ParseUnion() {
            var parts = new List<Str>();
            parts.Add(ParseInter());
            while (pos < len && input[pos] == '|') {
                pos++;
                parts.Add(ParseInter());
            }
            if (parts.Count == 1)
                return parts[0];
            return env.StrManager.MkUnion(parts);
        }

        Str ParseInter() {
            var parts = new List<Str>();
            parts.Add(ParseConcat());
            while (pos < len && input[pos] == '&') {
                pos++;
                parts.Add(ParseConcat());
            }
            if (parts.Count == 1)
                return parts[0];
            return env.StrManager.MkIntersection(parts);
        }

        Str ParseConcat() {
            var parts = new List<Str>();
            while (pos < len) {
                char c = input[pos];
                if (c == ')' || c == '|' || c == '&')
                    break;
                parts.Add(ParseRepeat());
            }
            if (parts.Count == 0)
                return env.EmptyStr;
            Str acc = parts[0];
            for (int i = 1; i < parts.Count; i++)
                acc = env.StrManager.Concat(acc, parts[i]);
            return acc;
        }

        Str ParseRepeat() {
            // handle prefix complement '~'
            int tildes = 0;
            while (pos < len && input[pos] == '~') {
                tildes++;
                pos++;
            }
            Str s = ParsePrimary();
            // apply postfix operators * and + as many times as present
            while (pos < len && (input[pos] == '*' || input[pos] == '+')) {
                if (input[pos] == '*')
                    s = env.StrManager.MkStar(s);
                else
                    s = env.StrManager.MkPlus(s);
                pos++;
            }
            // apply complements (each ~ is a complement)
            for (int i = 0; i < tildes; i++)
                s = env.StrManager.MkComplement(s);
            return s;
        }

        Str ParsePrimary() {
            if (pos >= len)
                return env.EmptyStr;
            char c = input[pos];
            if (c == '(') {
                pos++;
                Str inner = ParseUnion();
                if (pos >= len || input[pos] != ')')
                    throw new ArgumentException("Unmatched '('.", nameof(input));
                pos++;
                return inner;
            }
            pos++;
            if (char.IsUpper(c)) {
                return env.MkString(env.GetOrCreateStrVar(c.ToString()));
            }
            return env.MkString(new CharToken(c));
        }

        if (len == 0)
            return env.EmptyStr;
        var result = ParseUnion();
        if (pos != len)
            throw new ArgumentException("Unexpected character in regex at position " + pos, nameof(input));
        return result;
    }

    static bool CheckEquation(string lhs, string rhs) {
        Console.WriteLine($"Checking eq {lhs} = {rhs}");
        using Context ctx = new();
        using Solver solver = ctx.MkSimpleSolver();
        using Environment env = new(ctx);
        using SaturatingStringPropagator propagator = new(solver, env);
        var root = new NielsenNode(propagator.Graph);
        root.AddConstraint(new StrEq(ParseStr(lhs, env), ParseStr(rhs, env), new DependencyTracker(0)));
        LocalInfo info = new(root);
        bool res = propagator.Graph.Check(info);
        if (res)
            propagator.GetModel(info, out _);
        return res;
    }

    static bool CheckMembership(Environment env, string s, Str regex) => 
        CheckMembership(env, MkStrMem(ParseStr(s, env), regex, env.EmptyStr, 0));

    static bool CheckMembership(Environment env, params StrMem[] cnstrs) {
        Debug.Assert(cnstrs.Length > 0);
        Debug.Assert(cnstrs.Select((o, i) => (mem: o, id: i)).All(o => o.mem.Id == o.id));
        Console.WriteLine($"Checking memberships {string.Join(" & ", cnstrs.Select(o => o.Str + " in " + o.Regex))}");
        using Solver solver = env.Ctx.MkSimpleSolver();
        using SaturatingStringPropagator propagator = new(solver, env);
        var root = new NielsenNode(propagator.Graph);
        foreach (var cnstr in cnstrs) {
            root.AddConstraint(cnstr);
        }
        LocalInfo info = new(root) {
            NextRegexId = (uint)cnstrs.Length,
        };
        bool res = propagator.Graph.Check(info);
        if (res)
            propagator.GetModel(info, out _);
        return res;
    }

    static void CheckUnionEqual(CharacterSet s1, CharacterSet s2, CharacterSet expected) {
        var sum = s1.Clone();
        sum.Add(s2);
        if (sum.Equals(expected))
            return;
        Console.WriteLine($"Expected {s1} + {s2} is {expected} but got {sum}");
        Console.WriteLine(System.Environment.StackTrace);
        System.Environment.Exit(-1);
    }

    static void EqSAT(string lhs, string rhs) {
        if (CheckEquation(lhs, rhs))
            return;
        Console.WriteLine($"Expected SAT on \"{lhs}\" = \"{rhs}\" but got UNSAT");
        Console.WriteLine(System.Environment.StackTrace);
        System.Environment.Exit(-1);
    }

    static void EqUNSAT(string lhs, string rhs) {
        if (!CheckEquation(lhs, rhs))
            return;
        Console.WriteLine($"Expected UNSAT on \"{lhs}\" = \"{rhs}\" but got SAT");
        Console.WriteLine(System.Environment.StackTrace);
        System.Environment.Exit(-1);
    }

    static void MemSAT(Environment env, params StrMem[] cnstrs) {
        if (CheckMembership(env, cnstrs))
            return;
        Console.WriteLine($"Expected SAT on {string.Join(" & ", cnstrs.Select(o => o.Str + " in " + o.Regex))} but got UNSAT");
        Console.WriteLine(System.Environment.StackTrace);
        System.Environment.Exit(-1);
    }

    static void MemUNSAT(Environment env, params StrMem[] cnstrs) {
        if (!CheckMembership(env, cnstrs))
            return;
        Console.WriteLine($"Expected UNSAT on {string.Join(" & ", cnstrs.Select(o => o.Str + " in " + o.Regex))} but got SAT");
        Console.WriteLine(System.Environment.StackTrace);
        System.Environment.Exit(-1);
    }

    static void MemSAT(Environment env, string str, Str regex) {
        if (CheckMembership(env, str, regex))
            return;
        Console.WriteLine($"Expected SAT on \"{str}\" in \"{regex}\" but got UNSAT");
        Console.WriteLine(System.Environment.StackTrace);
        System.Environment.Exit(-1);
    }

    static void MemUNSAT(Environment env, string str, Str regex) {
        if (!CheckMembership(env, str, regex))
            return;
        Console.WriteLine($"Expected UNSAT on \"{str}\" in \"{regex}\" but got SAT");
        Console.WriteLine(System.Environment.StackTrace);
        System.Environment.Exit(-1);
    }

    static void CheckStrEquations() {
        if (!IsCheckStrEquations)
            return;
        Console.WriteLine("Checking String Equation...");
        
        EqSAT("abab", "XX");

        EqSAT("aX", "YX");
        EqSAT("aX", "Xa");
        EqUNSAT("aX", "Xb");
        EqSAT("abX", "Xba");
        EqSAT("XabY", "YbaX");
        EqUNSAT("abcX", "Xbac");
        EqUNSAT("aaX", "Xa");
        // UNSAT("XaY", "YbX");
        EqUNSAT("aa", "XXX");

        EqSAT("aX", "XY");
    }


    static void CheckCharacterSets() {
        if (!IsCheckCharacterSets)
            return;

        CheckUnionEqual(
            // [a,c] + [ab] = [a-c]
            new CharacterSet(new CharacterRange('a'), new CharacterRange('c')),
            new CharacterSet(new CharacterRange('a', 'b' + 1)),
            new CharacterSet(new CharacterRange('a', 'c' + 1))
        );
        CheckUnionEqual(
            // [ab] + [a,c] = [a-c]
            new CharacterSet(new CharacterRange('a', 'b' + 1)),
            new CharacterSet(new CharacterRange('a'), new CharacterRange('c')),
            new CharacterSet(new CharacterRange('a', 'c' + 1))
        );
        CheckUnionEqual(
            // [a,c] + [a,b,d] = [a-d]
            new CharacterSet(new CharacterRange('a'), new CharacterRange('c')),
            new CharacterSet(new CharacterRange('a', 'b' + 1), new CharacterRange('d')),
            new CharacterSet(new CharacterRange('a', 'd' + 1))
        );
        CheckUnionEqual(
            // [a,b,d] + [a,c] = [a-d]
            new CharacterSet(new CharacterRange('a', 'b' + 1), new CharacterRange('d')),
            new CharacterSet(new CharacterRange('a'), new CharacterRange('c')),
            new CharacterSet(new CharacterRange('a', 'd' + 1))
        );
        CheckUnionEqual(
            // [a,d] + [bc] = [a-d]
            new CharacterSet(new CharacterRange('a'), new CharacterRange('d')),
            new CharacterSet(new CharacterRange('b', 'c' + 1)),
            new CharacterSet(new CharacterRange('a', 'd' + 1))
        );
        CheckUnionEqual(
            // [a,e] + [bc] = [a-c,e]
            new CharacterSet(new CharacterRange('a'), new CharacterRange('e')),
            new CharacterSet(new CharacterRange('b', 'c' + 1)),
            new CharacterSet(new CharacterRange('a', 'c' + 1), new CharacterRange('e'))
        );
        CheckUnionEqual(
            // [bc] + [a,e] = [a-c,e]
            new CharacterSet(new CharacterRange('b', 'c' + 1)),
            new CharacterSet(new CharacterRange('a'), new CharacterRange('e')),
            new CharacterSet(new CharacterRange('a', 'c' + 1), new CharacterRange('e'))
        );
        CheckUnionEqual(
            // [a,e] + [cd] = [a,c-e]
            new CharacterSet(new CharacterRange('a'), new CharacterRange('e')),
            new CharacterSet(new CharacterRange('c', 'd' + 1)),
            new CharacterSet(new CharacterRange('a'), new CharacterRange('c', 'e' + 1))
        );
        CheckUnionEqual(
            // [cd] + [a,e] = [a,c-e]
            new CharacterSet(new CharacterRange('c', 'd' + 1)),
            new CharacterSet(new CharacterRange('a'), new CharacterRange('e')),
            new CharacterSet(new CharacterRange('a'), new CharacterRange('c', 'e' + 1))
        );
        CheckUnionEqual(
            // [a,c,e] + [a,ef] = [a,c,ef]
            new CharacterSet(new CharacterRange('a'), new CharacterRange('c'), new CharacterRange('e')),
            new CharacterSet(new CharacterRange('a'), new CharacterRange('e', 'f' + 1)),
            new CharacterSet(new CharacterRange('a'), new CharacterRange('c'), new CharacterRange('e', 'f' + 1))
        );
        CheckUnionEqual(
            // [a,ef] + [a,c,e]= [a,c,ef]
            new CharacterSet(new CharacterRange('a'), new CharacterRange('e', 'f' + 1)),
            new CharacterSet(new CharacterRange('a'), new CharacterRange('c'), new CharacterRange('e')),
            new CharacterSet(new CharacterRange('a'), new CharacterRange('c'), new CharacterRange('e', 'f' + 1))
        );
        CheckUnionEqual(
            // * + [e] = *
            CharacterSet.Full,
            new CharacterSet(new CharacterRange('e')),
            CharacterSet.Full
        );
        // TODO: Make merge tests
        // [0-96], [b-1000] };{ a }}}
        // [0-a], [c-1000]
        MinTerms m1 = new MinTerms(
            new CharacterSet(new CharacterRange(0, 96 + 1), new CharacterRange('b', 1000 + 1)),
            new CharacterSet(new CharacterRange('a'))
        );
        MinTerms m2 = new MinTerms(
            new CharacterSet(new CharacterRange(0, 'a' + 1), new CharacterRange('c', 1000 + 1))
        );
        m1.Merge(m2);
    }

    static void CheckRegexMatching() {
        if (!IsCheckRegexMatching)
            return;
        Console.WriteLine("Checking Regex Matching...");
        using Context ctx = new();
        using Environment env = new Environment(ctx);

        MemSAT(env, "", ParseRegex("", env));
        MemUNSAT(env, "a", ParseRegex("", env));

        MemSAT(env, "X", ParseRegex("", env));

        MemSAT(env, "", ParseRegex("a*", env));
        MemSAT(env, "aaaa", ParseRegex("a*", env));
        MemUNSAT(env, "b", ParseRegex("a*", env));
        MemSAT(env, "abbb", ParseRegex("ab*", env));

        MemSAT(env, "ab", ParseRegex("(ab)+", env));
        MemSAT(env, "ababab", ParseRegex("(ab)+", env));
        MemUNSAT(env, "", ParseRegex("(ab)+", env));

        MemSAT(env, "", ParseRegex("()", env));
        MemSAT(env, "", ParseRegex("()*", env));
        MemUNSAT(env, "a", ParseRegex("()*", env));
        
        MemUNSAT(env, "a", ParseRegex("~a", env));
        MemSAT(env, "b", ParseRegex("~a", env));

        MemSAT(env, "a", ParseRegex("~(~a)", env));

        MemUNSAT(env, "a", ParseRegex("a&(~a)", env));
        MemUNSAT(env, "a", ParseRegex("(a|b)&(~a)", env));
        MemSAT(env, "b", ParseRegex("(a|b)&(~a)", env));

        MemSAT(env, "ab", ParseRegex("ab", env));
        MemSAT(env, "a", ParseRegex("a|b", env));
        MemSAT(env, "b", ParseRegex("a|b", env));
        MemUNSAT(env, "ab", ParseRegex("a|b", env));

        MemSAT(env, "b", ParseRegex("(a|b)|(c|d)", env));
        MemSAT(env, "c", ParseRegex("(a|b)|(c|d)", env));
        MemUNSAT(env, "e", ParseRegex("(a|b)|(c|d)", env));
        MemSAT(env, "b", ParseRegex("(a|b)&(~a|b)", env));
        MemUNSAT(env, "a", ParseRegex("(a|b)&(~a|b)", env));

        MemSAT(env, "abababab", ParseRegex("(ab)*", env));
        MemSAT(env, "abab", ParseRegex("(ab)*", env));
        MemUNSAT(env, "aba", ParseRegex("(ab)*", env));

        MemSAT(env, "c", ParseRegex("(a|b|c)&(c|d)", env));
        MemUNSAT(env, "b", ParseRegex("(a|b|c)&(c|d)", env));

        MemSAT(env, "abab", ParseRegex("((ab)|(ba))+", env));
        MemUNSAT(env, "a", ParseRegex("((ab)|(ba))+", env));

        MemSAT(env, "c", ParseRegex("(~a)&(c|b)", env));

        MemUNSAT(env, "a", ParseRegex("~(a|b)", env));
        MemSAT(env, "c", ParseRegex("~(a|b)", env));
    }

    static StrMem MkStrMem(Str str, Str regex, Str history, uint id) {
        return new StrMem(str, regex, history, id, new DependencyTracker(0));
    }

    static void CheckStrMembership() {
        if (!IsCheckStrMembership)
            return;
        Console.WriteLine("Checking String Membership...");
        using Context ctx = new();
        using Environment env = new Environment(ctx);

        // x \in (~(ab))*cab
        MemSAT(env, "X", ParseRegex("(~(ab))*cab", env));

        MemUNSAT(env,
            // x \in a* && x \in b+
            MkStrMem(ParseStr("X", env), ParseRegex("a*", env), env.EmptyStr, 0),
            MkStrMem(ParseStr("X", env), ParseRegex("a*", env), env.EmptyStr, 0),
            MkStrMem(ParseStr("X", env), ParseRegex("b+", env), env.EmptyStr, 1)
        );
        MemSAT(env,
            // x \in a*b* && y \in a*b*
            MkStrMem(ParseStr("X", env), ParseRegex("a*b*", env), env.EmptyStr, 0),
            MkStrMem(ParseStr("Y", env), ParseRegex("a*b*", env), env.EmptyStr, 1)
        );
        MemSAT(env,
            // x \in a* && y \in (ab)+
            MkStrMem(ParseStr("X", env), ParseRegex("a*", env), env.EmptyStr, 0),
            MkStrMem(ParseStr("Y", env), ParseRegex("(ab)+", env), env.EmptyStr, 1)
        );
        MemUNSAT(env,
            // x \in (ab)+ && x \in a*
            MkStrMem(ParseStr("X", env), ParseRegex("(ab)+", env), env.EmptyStr, 0),
            MkStrMem(ParseStr("X", env), ParseRegex("a*", env), env.EmptyStr, 1)
        );
        MemUNSAT(env, "XaX",
            // xax \in (aa)*
            ParseRegex("(aa)*", env)
        );

        MemSAT(env, "aX",
            // ax \in a(a)*
            ParseRegex("aa*", env)
        );
        MemUNSAT(env,
            // x \in (aa)*a && x \in (aa)*
            MkStrMem(ParseStr("X", env),
                ParseRegex("(aa)*a", env), env.EmptyStr, 0
            ),
            MkStrMem(ParseStr("X", env),
                ParseRegex("(aa)*", env), env.EmptyStr, 1
            )
        );
        MemSAT(env,
            // x \in (aa)*aa && x \in (aa)*
            MkStrMem(ParseStr("X", env),
                ParseRegex("(aa)*aa", env), env.EmptyStr, 0
            ),
            MkStrMem(ParseStr("X", env), ParseRegex("(aa)*", env), env.EmptyStr, 1)
        );
        MemSAT(env, "Xa",
            // xa \in a(a)*
            ParseRegex("aa*", env)
        );
        MemSAT(env, "Xa",
            // xa \in a(a)*a
            ParseRegex("aa*a", env)
        );
        MemUNSAT(env, "bX",
            // bx \in a(a)*
            ParseRegex("a*a", env)
        );
        MemUNSAT(env, "bX",
            // bx \in (a)*
            ParseRegex("a*", env)
        );
        MemUNSAT(env, "bX",
            // bx \in (a)*a
            ParseRegex("a*a", env)
        );
        MemSAT(env, "bX",
            // bx \in (b)*a
            ParseRegex("b*a", env)
        );
        MemSAT(env, "bXb",
            // bxb \in (b)*a(b)*
            ParseRegex("b*ab*", env)
        );
        MemSAT(env, "bXbb",
            // bxbb \in (b)*a(b)*
            ParseRegex("b*ab*", env)
        );
        MemSAT(env, "XX",
            // xx \in a(a)*
            ParseRegex("aa*", env)
        );
        MemSAT(env, "XaX",
            // xax \in aa(a)*
            ParseRegex("aaa*", env)
        );
        MemSAT(env, "XX",
            // xx \in aaa(a)*
            ParseRegex("aaaa*", env)
        );
        MemUNSAT(env, "XbX",
            // xbx \in (a)*
            ParseRegex("a*", env)
        );
        MemSAT(env, "XbX",
            // xbx \in (a)*(b)*
            ParseRegex("a*b*", env)
        );
        MemSAT(env, "XbX",
            // xbx \in (a)*(b)*(a)*a
            ParseRegex("a*b*a*a", env)
        );
        MemUNSAT(env, "XabX",
            // xabx \in (aba)*
            ParseRegex("(aba)*", env)
        );
        MemUNSAT(env, "XaX",
            // xax \in (ab)*
            ParseRegex("(ab)*", env)
        );
        MemSAT(env, "X",
            // x \in a|b
            ParseRegex("a|b", env)
        );
        MemUNSAT(env, "XX",
            // xx \in a|b
            ParseRegex("a|b", env)
        );
        MemUNSAT(env, "XX",
            // xx \in (ab)|(ba)
            ParseRegex("(ab)|(ba)", env)
        );
        MemSAT(env, "XX",
            // xx \in ((ab)|(ba))((ba)|(ab))
            ParseRegex("(ab|ba)(ba|ab)", env)
        );
        MemUNSAT(env, "XX",
            // xx \in ((ab)|(ba))((aa)|(bb))
            ParseRegex("(ab|ba)(aa|bb)", env)
        );
        MemUNSAT(env, "bXbX",
            // bxbx \in (a)*(b)*(a)*a
            ParseRegex("a*b*a*a", env)
        );
        MemSAT(env, "XdX",
            // xdx \in (a|b)*da(a|c)*
            ParseRegex("(a|b)*da(a|c)*", env)
        );
        // These require more sophisticated splittings
        MemUNSAT(env, "XbX",
            // xbx \in (ab)*
            ParseRegex("(ab)*", env)
        );
        MemUNSAT(env,
            // xabx \in (ab)*
            // xbabx \in a(ba)*
            [
                MkStrMem(
                    ParseStr("XabX", env),
                    ParseRegex("(ab)*", env), env.EmptyStr, 0
                ),
                MkStrMem(
                    ParseStr("XbabX", env),
                    ParseRegex("a(ba)*", env), env.EmptyStr, 1
                ),
            ]
        );
        MemUNSAT(env, "XX",
            // xx \in (aba)*a
            ParseRegex("(aba)*a", env)
        );
        MemSAT(env, "XX",
            // xx \in (((ab)|(ba)))+aa
            ParseRegex("(((ab)|(ba)))+aa", env)
        );
        MemUNSAT(env, "XX",
            // xx \in (ab)*a
            ParseRegex("(ab)*a", env)
        );
        MemUNSAT(env, "XX",
            // xx \in (a(a|b))*a
            ParseRegex("(a(a|b))*a", env)
        );
        MemUNSAT(env, "XX",
            // xx \in (a(a|(aaa)))*a
            ParseRegex("(a(a|(aaa)))*a", env)
        );
        MemSAT(env, "XX",
            // xx \in (((ab)|(ba)))+aa
            ParseRegex("(((ab)|(ba)))+aa", env)
        );
        MemUNSAT(env, "XX",
            // xx \in (((ab)|(ba)))+aaaa
            ParseRegex("(((ab)|(ba)))+aaaa", env)
        );
        MemSAT(env, "XX",
            // xx \in (((ab)|(ba)))*aaaa
            ParseRegex("(((ab)|(ba)))*aaaa", env)
        );

        MemUNSAT(env,
            // x \in a+ && x \in b+
            MkStrMem(ParseStr("X", env), ParseRegex("a+", env), env.EmptyStr, 0),
            MkStrMem(ParseStr("X", env), ParseRegex("b+", env), env.EmptyStr, 1)
        );

        MemUNSAT(env,
            // x \in (a|b) && xx \in (a|b)
            MkStrMem(ParseStr("X", env), ParseRegex("a|b", env), env.EmptyStr, 0),
            MkStrMem(ParseStr("XX", env), ParseRegex("a|b", env), env.EmptyStr, 1)
        );

        MemUNSAT(env,
            // x \in (ab)+ && xx \in a*
            MkStrMem(ParseStr("X", env), ParseRegex("(ab)+", env), env.EmptyStr, 0),
            MkStrMem(ParseStr("XX", env), ParseRegex("a*", env), env.EmptyStr, 1)
        );

        MemSAT(env,
            // x \in a* && y \in b* && xy \in (ab)+
            MkStrMem(ParseStr("X", env), ParseRegex("a*", env), env.EmptyStr, 0),
            MkStrMem(ParseStr("Y", env), ParseRegex("b*", env), env.EmptyStr, 1),
            MkStrMem(ParseStr("XY", env), ParseRegex("(ab)+", env), env.EmptyStr, 2)
        );

        MemUNSAT(env,
            // x \in a* && x \in ~(a*)
            MkStrMem(ParseStr("X", env), ParseRegex("a*", env), env.EmptyStr, 0),
            MkStrMem(ParseStr("X", env), ParseRegex("~(a*)", env), env.EmptyStr, 1)
        );

        MemSAT(env,
            // x \in (ab)* && x \in (ab)+ 
            MkStrMem(ParseStr("X", env), ParseRegex("(ab)*", env), env.EmptyStr, 0),
            MkStrMem(ParseStr("X", env), ParseRegex("(ab)+", env), env.EmptyStr, 1)
        );

        MemSAT(env,
            // x \in ~(a|b) && x \in (c|d)
            MkStrMem(ParseStr("X", env), ParseRegex("~(a|b)", env), env.EmptyStr, 0),
            MkStrMem(ParseStr("X", env), ParseRegex("(c|d)", env), env.EmptyStr, 1)
        );

        // x \in (a|b)* && xx \in (ab)+
        MemSAT(env,
            MkStrMem(ParseStr("X", env), ParseRegex("(a|b)*", env), env.EmptyStr, 0),
            MkStrMem(ParseStr("XX", env), ParseRegex("(ab)+", env), env.EmptyStr, 1)
        );

        MemSAT(env,
            // x \in a+ && y \in b* && xyyx \in (ab)*(ba)*
            MkStrMem(ParseStr("X", env), ParseRegex("a+", env), env.EmptyStr, 0),
            MkStrMem(ParseStr("Y", env), ParseRegex("b*", env), env.EmptyStr, 1),
            MkStrMem(ParseStr("XYYX", env), ParseRegex("(ab)*(ba)*", env), env.EmptyStr, 2)
        );

        MemSAT(env,
            // x \in (ab)+ && xx in (ab)+
            MkStrMem(ParseStr("X", env), ParseRegex("(ab)+", env), env.EmptyStr, 0),
            MkStrMem(ParseStr("XXX", env), ParseRegex("(ab)+", env), env.EmptyStr, 1)
        );

        MemUNSAT(env,
            // x \in (a|b) && x \in ~(a|b)
            MkStrMem(ParseStr("X", env), ParseRegex("(a|b)", env), env.EmptyStr, 0),
            MkStrMem(ParseStr("X", env), ParseRegex("~(a|b)", env), env.EmptyStr, 1)
        );

        MemSAT(env,
            // x \in a+ && Y \in b+ && xy in (ab)+
            MkStrMem(ParseStr("X", env), ParseRegex("a+", env), env.EmptyStr, 0),
            MkStrMem(ParseStr("Y", env), ParseRegex("b+", env), env.EmptyStr, 1),
            MkStrMem(ParseStr("XY", env), ParseRegex("(ab)+", env), env.EmptyStr, 2)
        );

        MemSAT(env,
            // xbx \in a*b*
            MkStrMem(ParseStr("XbX", env), ParseRegex("a*b*", env), env.EmptyStr, 0)
        );

        MemUNSAT(env,
            // x \in a+ && xbx \in b*
            MkStrMem(ParseStr("X", env), ParseRegex("a+", env), env.EmptyStr, 0),
            MkStrMem(ParseStr("XbX", env), ParseRegex("b*", env), env.EmptyStr, 1)
        );

        MemSAT(env,
            // axb \in a(a|b)*b
            MkStrMem(ParseStr("aXb", env), ParseRegex("a(a|b)*b", env), env.EmptyStr, 0)
        );

        MemSAT(env,
            // xyx && x \in a+, y \in b+ && xyx \in (ab)*(ba)*
            MkStrMem(ParseStr("X", env), ParseRegex("a+", env), env.EmptyStr, 0),
            MkStrMem(ParseStr("Y", env), ParseRegex("b+", env), env.EmptyStr, 1),
            MkStrMem(ParseStr("XYX", env), ParseRegex("(ab)*(ba)*", env), env.EmptyStr, 2)
        );

        MemSAT(env,
            // xx \in (ab|ba)+ && x \in (a|b)+
            MkStrMem(ParseStr("XX", env), ParseRegex("(ab|ba)+", env), env.EmptyStr, 0),
            MkStrMem(ParseStr("X", env), ParseRegex("(a|b)+", env), env.EmptyStr, 1)
        );

        MemSAT(env,
            // x \in a* && x \in a+
            MkStrMem(ParseStr("X", env), ParseRegex("a*", env), env.EmptyStr, 0),
            MkStrMem(ParseStr("X", env), ParseRegex("a+", env), env.EmptyStr, 1)
        );

        MemUNSAT(env,
            // x \in "" && xbx \in a*baa*
            MkStrMem(ParseStr("X", env), env.EmptyStr, env.EmptyStr, 0),
            MkStrMem(ParseStr("XbX", env), ParseRegex("a*baa*", env), env.EmptyStr, 1)
        );

        MemSAT(env,
            // xxxx \in aaaaa*
            MkStrMem(ParseStr("XXXX", env), ParseRegex("aaaaa*", env), env.EmptyStr, 0)
        );

        MemUNSAT(env,
            // xxxx \in aaa(aa)*
            MkStrMem(ParseStr("XXXX", env), ParseRegex("aaa(aa)*", env), env.EmptyStr, 0)
        );

        MemUNSAT(env,
            // xxxx \in ab
            MkStrMem(ParseStr("XXXX", env), ParseRegex("ab", env), env.EmptyStr, 0)
        );
        MemUNSAT(env,
            // xxxx \in abab
            MkStrMem(ParseStr("XXXX", env), ParseRegex("abab", env), env.EmptyStr, 0)
        );
        
        MemSAT(env,
            // xxxx \in a(ba)*b
            MkStrMem(ParseStr("XXXX", env), ParseRegex("a(ba)*b", env), env.EmptyStr, 0)
        );

        MemUNSAT(env,
            // xxxx \in a(ab)*b
            MkStrMem(ParseStr("XXXX", env), ParseRegex("a(ab)*b", env), env.EmptyStr, 0)
        );

        MemUNSAT(env,
            // xyyx \in ab
            MkStrMem(ParseStr("XYYX", env), ParseRegex("ab", env), env.EmptyStr, 0)
        );

        MemUNSAT(env,
            // xyyx \in a(ab)*b
            MkStrMem(ParseStr("XYYX", env), ParseRegex("a(ab)*b", env), env.EmptyStr, 0)
        );

        MemUNSAT(env,
            // xyyx \in a+b+
            MkStrMem(ParseStr("XYYX", env), ParseRegex("a+b+", env), env.EmptyStr, 0)
        );

        // xax \in a(a|b)*a
        MemSAT(env, "XaX", ParseRegex("a(a|b)*a", env));

        // xby \in a+b* && x in a+ && y in b+
        MemSAT(env,
            MkStrMem(ParseStr("XbY", env), ParseRegex("a+b*", env), env.EmptyStr, 0),
            MkStrMem(ParseStr("X", env), ParseRegex("a*", env), env.EmptyStr, 1),
            MkStrMem(ParseStr("Y", env), ParseRegex("b+", env), env.EmptyStr, 2)
        );

        MemUNSAT(env,
            // xby \in (ab)+ && x \in a+ && y \in b+
            MkStrMem(ParseStr("X", env), ParseRegex("a+", env), env.EmptyStr, 0),
            MkStrMem(ParseStr("Y", env), ParseRegex("b+", env), env.EmptyStr, 1),
            MkStrMem(ParseStr("XbY", env), ParseRegex("(ab)+", env), env.EmptyStr, 2)
        );

        MemUNSAT(env,
            // xby \in (ab)* && x \in ((""|a)b)* && y \in (a(""|b))*
            MkStrMem(ParseStr("X", env), ParseRegex("((()|a)b)*", env), env.EmptyStr, 0),
            MkStrMem(ParseStr("Y", env), ParseRegex("(a(()|b))*", env), env.EmptyStr, 1),
            MkStrMem(ParseStr("XbY", env), ParseRegex("(ab)*", env), env.EmptyStr, 2)
        );

        MemSAT(env,
            // xby \in (ab)* && x \in (a(""|b))* && y \in (ab)*
            MkStrMem(ParseStr("X", env), ParseRegex("(a(()|b))*", env), env.EmptyStr, 0),
            MkStrMem(ParseStr("Y", env), ParseRegex("(ab)*", env), env.EmptyStr, 1),
            MkStrMem(ParseStr("XbY", env), ParseRegex("(ab)*", env), env.EmptyStr, 2)
        );
        MemUNSAT(env,
            // xby \in (ab)* && x \in (ab)* && y \in ((""|a)b)*
            MkStrMem(ParseStr("X", env), ParseRegex("(ab)*", env), env.EmptyStr, 0),
            MkStrMem(ParseStr("Y", env), ParseRegex("((()|a)b)*", env), env.EmptyStr, 1),
            MkStrMem(ParseStr("XbY", env), ParseRegex("(ab)*", env), env.EmptyStr, 2)
        );

        MemUNSAT(env,
            // xby \in (ab)* && x \in (ab)* && y \in (ab)*
            MkStrMem(ParseStr("X", env), ParseRegex("(ab)*", env), env.EmptyStr, 0),
            MkStrMem(ParseStr("Y", env), ParseRegex("(ab)*", env), env.EmptyStr, 1),
            MkStrMem(ParseStr("XbY", env), ParseRegex("(ab)*", env), env.EmptyStr, 2)
        );

        // x \in a+ && y \in b+ && z \in c+ && xyz \in (abc)+
        MemSAT(env,
            MkStrMem(ParseStr("X", env), ParseRegex("a+", env), env.EmptyStr, 0),
            MkStrMem(ParseStr("Y", env), ParseRegex("b+", env), env.EmptyStr, 1),
            MkStrMem(ParseStr("Z", env), ParseRegex("c+", env), env.EmptyStr, 2),
            MkStrMem(ParseStr("XYZ", env), ParseRegex("(abc)+", env), env.EmptyStr, 3)
        );

        MemSAT(env,
            // xaybz \in a*b*c* && x \in a* && y \in b* && z \in c*
            MkStrMem(ParseStr("XaYbZ", env), ParseRegex("a*b*c*", env), env.EmptyStr, 0),
            MkStrMem(ParseStr("X", env), ParseRegex("a*", env), env.EmptyStr, 1),
            MkStrMem(ParseStr("Y", env), ParseRegex("b*", env), env.EmptyStr, 2),
            MkStrMem(ParseStr("Z", env), ParseRegex("c*", env), env.EmptyStr, 3)
        );

        MemSAT(env,
            // axbyc \in a(a|b|c)*c
            MkStrMem(ParseStr("aXbYc", env), ParseRegex("a(a|b|c)*c", env), env.EmptyStr, 0)
        );

        MemSAT(env,
            // x \in (a|b)* && y \in (b|c)* && z \in (c|a)* && xyz \in (abc)+
            MkStrMem(ParseStr("X", env), ParseRegex("(a|b)*", env), env.EmptyStr, 0),
            MkStrMem(ParseStr("Y", env), ParseRegex("(b|c)*", env), env.EmptyStr, 1),
            MkStrMem(ParseStr("Z", env), ParseRegex("(c|a)*", env), env.EmptyStr, 2),
            MkStrMem(ParseStr("XYZ", env), ParseRegex("(abc)+", env), env.EmptyStr, 3)
        );
    }

    static void ParikhUNSAT(string lhs, string rhs) {
        Console.WriteLine($"Checking Parikh {lhs} = {rhs}");
        using Context ctx = new();
        using Solver solver = ctx.MkSimpleSolver();
        using Environment env = new(ctx);
        if (!StrEq.CheckMultiSequenceParikh(env, ParseStr(lhs, env), ParseStr(rhs, env)))
            return;
        Console.WriteLine($"Expected UNSAT (Parikh) on \"{lhs}\" = \"{rhs}\"");
        System.Environment.Exit(-1);
    }

    static void CheckParikh() {
        if (!IsCheckParikh)
            return;
        // Single characters are covered in the string solver only; only proper multi-sequence checks
        Console.WriteLine("Checking Parikh Images...");
        ParikhUNSAT("abcX", "Xbac");
        ParikhUNSAT("XabcY", "YbacX");
        ParikhUNSAT("XXabcYY", "YYbacXX");
        ParikhUNSAT("XXacdYYb", "YYabcdXX");
        ParikhUNSAT("YaXaaabbbbYX", "XYababababXY");
    }
}