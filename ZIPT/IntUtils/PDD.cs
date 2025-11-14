using Microsoft.Z3;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.Numerics;
using System.Runtime.CompilerServices;
using System.Text;
using ZIPT.Constraints;
using ZIPT.Strings.Tokens;

namespace ZIPT.IntUtils;

// idea taken from Z3's PDD<T> (Polynomial Decision Diagram)
// https://github.com/Z3Prover/z3/blob/polysat/src/math/dd/dd_pdd.h
public class PDD<T> : IComparable<PDD<T>> where T: struct, INumberBase<T>, IComparable<T> {

    public class PDDManager {

        readonly Dictionary<(NamedInt, PDD<T>, PDD<T>), PDD<T>> varPDDCache = [];
        readonly Dictionary<T, PDD<T>> constPDDCache = [];
        public PDD<T> Zero { get; }
        public PDD<T> One { get; }
        public PDD<T> Two { get; }

        public PDDManager() {
            Zero = MkPDD(T.Zero);
            One = MkPDD(T.One);
            Two = MkPDD(T.One + T.One);
        }

        public PDD<T> MkPDD(T value) {
            if (constPDDCache.TryGetValue(value, out var cached))
                return cached;
            var c = new PDD<T>(this, value);
            constPDDCache[value] = c;
            return c;
        }

        public PDD<T> MkPDD(NamedInt var, PDD<T> thenBranch, PDD<T> elseBranch) {
            if (thenBranch.IsZero)
                return elseBranch;

            var key = (var, thenBranch, elseBranch);
            if (varPDDCache.TryGetValue(key, out var cached))
                return cached;

            var node = new PDD<T>(var, thenBranch, elseBranch);
            varPDDCache[key] = node;
            return node;
        }

        public PDD<T> MkPDD(NamedInt v) =>
            MkPDD(v, One, Zero);

    }

    public PDDManager Manager { get; }
    // TODO: IdSet?

    public bool Marker { get; set; }
    public NamedInt? Var { get; }
    public PDD<T>? Then { get; }
    public PDD<T>? Else { get; }
    public T? Const { get; }

    public T ConstOffset
    {
        get
        {
            PDD<T> current = this;
            while (!current.Const.HasValue) {
                current = current.Else!;
            }
            return current.Const!.Value;
        }
    }

    [Pure]
    public int DominatorSign => !Const.HasValue || T.IsZero(Const.Value)
        ? 0
        : T.IsPositive(Const.Value)
            ? 1
            : -1;

    public PDD<T> Zero => Manager.Zero;
    public PDD<T> One => Manager.One;

    public bool IsNormal
    {
        [MethodImpl(MethodImplOptions.AggressiveInlining), Pure]
        get
        {
            if (IsZero)
                return true;
            var c = this;
            while (!c.IsConst) {
                c = c.Then!; // skip to the next branch
            }
            Debug.Assert(c.Const.HasValue);
            Debug.Assert(!T.IsZero(c.Const.Value));
            return T.IsPositive(c.Const.Value);
        }
    }

    [Pure]
    public bool IsConst => Const.HasValue;


    [MethodImpl(MethodImplOptions.AggressiveInlining), Pure]
    public bool TryGetConst(out T val) {
        val = default;
        if (!IsConst)
            return false;
        val = Const!.Value;
        return true;
    }

    [Pure]
    public bool IsLinear {
        get
        {
            Stack<PDD<T>> todo = new();
            todo.Push(this);
            while (todo.Count > 0) {
                var p = todo.Pop();
                if (p.IsConst)
                    continue;
                Debug.Assert(p.Var is not null && p.Then is not null && p.Else is not null);
                var then = p.Then;
                var @else = p.Else;
                if (!then.IsConst) {
                    Debug.Assert(then.Var is not null && then.Then is not null && then.Else is not null);
                    if (then.Var.Equals(p.Var))
                        return false;
                    todo.Push(then);
                }
                if (@else.IsConst) 
                    continue;
                Debug.Assert(@else.Var is not null && @else.Then is not null && @else.Else is not null);
                if (@else.Var.Equals(p.Var))
                    return false;
                todo.Push(@else);
            }
            return true;
        }
    }

    PDD(NamedInt var, PDD<T> thenBranch, PDD<T> elseBranch) {
        Log.Caller(nameof(Manager.MkPDD));
        Debug.Assert(ReferenceEquals(thenBranch.Manager, elseBranch.Manager));
        Manager = thenBranch.Manager;
        Var = var;
        Then = thenBranch;
        Else = elseBranch;
        Const = null;
    }

    PDD(PDDManager manager, T value) {
        Log.Caller(nameof(Manager.MkPDD));
        Manager = manager;
        Var = null;
        Then = null;
        Else = null;
        Const = value;
    }

    public bool IsZero => IsConst && Const!.Value.Equals(T.Zero);
    public bool IsOne => IsConst && Const!.Value.Equals(T.One);


    [MethodImpl(MethodImplOptions.AggressiveInlining), Pure]
    public PDD<T> Add(PDD<T> b) => Add(this, b);

    [MethodImpl(MethodImplOptions.AggressiveInlining), Pure]
    public PDD<T> Add(T i) => Add(this, Manager.MkPDD(i));

    [Pure]
    public static PDD<T> Add(PDD<T> a, PDD<T> b) {
        Debug.Assert(ReferenceEquals(a.Manager, b.Manager));
        PDDManager m = a.Manager;
        if (a.IsConst && b.IsConst)
            return m.MkPDD(a.Const!.Value + b.Const!.Value);

        if (a == b)
            return m.Two.Mul(a);
        if (a.IsZero)
            return b;
        if (b.IsZero)
            return a;

        if (a.IsConst)
            // happens at most once - recursion is fine
            return Add(b, a); // Const on the right

        Debug.Assert(a.Var is not null && a.Then is not null && a.Else is not null);

        if (b.IsConst)
            return m.MkPDD(a.Var, a.Then, Add(a.Else, b));

        Debug.Assert(b.Var is not null && b.Then is not null && b.Else is not null);

        int cmp = a.Var.CompareTo(b.Var);

        return cmp switch {
            > 0 => m.MkPDD(b.Var, b.Then, Add(a, b.Else)),
            < 0 => m.MkPDD(a.Var, a.Then, Add(a.Else, b)),
            _ => m.MkPDD(a.Var, Add(a.Then, b.Then), Add(a.Else, b.Else)),
        };
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining), Pure]
    public PDD<T> Sub(PDD<T> b) => Sub(this, b);

    // TODO: Optimize this
    [MethodImpl(MethodImplOptions.AggressiveInlining), Pure]
    public static PDD<T> Sub(PDD<T> a, PDD<T> b) => Add(a, Negate(b));

    [MethodImpl(MethodImplOptions.AggressiveInlining), Pure]
    public PDD<T> Negate() => Negate(this);

    [MethodImpl(MethodImplOptions.AggressiveInlining), Pure]
    public static PDD<T> Negate(PDD<T> p) =>
        p.IsConst 
            ? p.Manager.MkPDD(-p.Const!.Value) 
            : p.Manager.MkPDD(p.Var!, Negate(p.Then!), Negate(p.Else!));

    [MethodImpl(MethodImplOptions.AggressiveInlining), Pure]
    public PDD<T> Mul(PDD<T> b) => Mul(this, b);

    [Pure]
    public static PDD<T> Mul(PDD<T> a, PDD<T> b) {
        Debug.Assert(ReferenceEquals(a.Manager, b.Manager));
        PDDManager m = a.Manager;
        if (a.IsConst && b.IsConst)
            return m.MkPDD(a.Const!.Value * b.Const!.Value);

        if (a.IsZero || b.IsZero)
            return m.Zero;
        if (a.IsConst)
            return Mul(b, a);

        Debug.Assert(a.Var is not null && a.Then is not null && a.Else is not null);

        if (b.IsConst)
            return m.MkPDD(a.Var, Mul(a.Then, b), Mul(a.Else, b));

        Debug.Assert(b.Var is not null && b.Then is not null && b.Else is not null);

        int cmp = a.Var.CompareTo(b.Var);

        switch (cmp) {
            case < 0:
                return m.MkPDD(a.Var, Mul(a.Then, b), Mul(a.Else, b));
            case > 0:
                return m.MkPDD(b.Var, Mul(a, b.Then), Mul(a, b.Else));
            default:
                var thenProd = Mul(a.Then, b.Then);
                var mix = Add(Mul(a.Then, b.Else), Mul(a.Else, b.Then));
                var elseProd = Mul(a.Else, b.Else);
                return m.MkPDD(a.Var, thenProd, Add(mix, elseProd));
        }
    }

    // Multiply the PDDs and introduce definitions to have the result linear
    [Pure]
    public static PDD<T> MulByDefinitions(PDD<T> a, PDD<T> b, Dictionary<NamedInt, PDD<T>> definitions) {
        Debug.Assert(a.IsLinear);
        Debug.Assert(b.IsLinear);
        Debug.Assert(ReferenceEquals(a.Manager, b.Manager));
        PDDManager m = a.Manager;
        if (a.IsConst && b.IsConst)
            return m.MkPDD(a.Const!.Value * b.Const!.Value);

        if (a.IsZero || b.IsZero)
            return m.Zero;
        if (a.IsConst)
            return MulByDefinitions(b, a, definitions);

        Debug.Assert(a.Var is not null && a.Then is not null && a.Else is not null);

        if (b.IsConst)
            return m.MkPDD(a.Var, MulByDefinitions(a.Then, b, definitions), MulByDefinitions(a.Else, b, definitions));

        Debug.Assert(b.Var is not null && b.Then is not null && b.Else is not null);

        throw new NotImplementedException();
        int cmp = a.Var.CompareTo(b.Var);

        switch (cmp) {
            case < 0:
                return m.MkPDD(a.Var, MulByDefinitions(a.Then, b, definitions), MulByDefinitions(a.Else, b, definitions));
            case > 0:
                return m.MkPDD(b.Var, MulByDefinitions(a, b.Then, definitions), MulByDefinitions(a, b.Else, definitions));
            default:
                var thenProd = MulByDefinitions(a.Then, b.Then, definitions);
                var mix = Add(MulByDefinitions(a.Then, b.Else, definitions), MulByDefinitions(a.Else, b.Then, definitions));
                var elseProd = MulByDefinitions(a.Else, b.Else, definitions);
                return m.MkPDD(a.Var, thenProd, Add(mix, elseProd));
        }
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining), Pure]
    public PDD<T> Substitute(NamedInt targetVar, PDD<T> replacement) =>
        Substitute(this, targetVar, replacement);

    [Pure]
    public static PDD<T> Substitute(PDD<T> p, NamedInt targetVar, PDD<T> replacement) {
        if (p.IsConst)
            return p;

        Debug.Assert(p.Var is not null && p.Then is not null && p.Else is not null);
        PDDManager m = p.Manager;

        int cmp = p.Var.CompareTo(targetVar);

        switch (cmp) {
            // p.Var > targetVar: target not in this branch
            case > 0:
                return m.MkPDD(p.Var, Substitute(p.Then, targetVar, replacement), Substitute(p.Else, targetVar, replacement));
            // p.Var < targetVar: proceed deeper
            case < 0:
                return m.MkPDD(p.Var, Substitute(p.Then, targetVar, replacement), Substitute(p.Else, targetVar, replacement));
            default:
                // p.Var == targetVar: replace x * Then + Else with replacement * Then + Else
                var replacedThen = Mul(replacement, Substitute(p.Then, targetVar, replacement));
                var replacedElse = Substitute(p.Else, targetVar, replacement);
                return Add(replacedThen, replacedElse);
        }
    }

    [Pure]
    public static PDD<BigInteger> Substitute(PDD<BigInteger> p, Interpretation itp) {
        if (p.IsConst)
            return p;

        Debug.Assert(p.Var is not null && p.Then is not null && p.Else is not null);

        var then = Substitute(p.Then, itp);
        var @else = Substitute(p.Else, itp);
        var newVal = p.Manager.MkPDD(p.Var);
        if (p.Var is LenVar lv) {
            if (itp.Substitution.TryGetValue(lv.Var, out var newStr))
                newVal = LenVar.MkLenPoly(newStr.Str, itp.Env);
        }
        else if (p.Var is IntVar iv) {
            if (itp.IntVal.TryGetValue(iv, out var value))
                newVal = p.Manager.MkPDD(value);
        }
        return PDD<BigInteger>.Add(PDD<BigInteger>.Mul(newVal, then), @else);
    }

    // returns 1 if all coefficients are positive (or zero),
    // -1 if all coefficients are negative, and
    // 0 if there are both positive and negative coefficients
    [Pure]
    public static int GetPolarity(PDD<BigInteger> p) {
        if (p.IsZero)
            return 1;
        Stack<PDD<BigInteger>> stack = [];
        List<PDD<BigInteger>> marked = [];
        Debug.Assert(!p.Marker);
        stack.Push(p);
        bool pos = true;
        bool neg = true;
        while (stack.Count > 0) {
            p = stack.Pop();
            if (p.Marker)
                continue;
            p.Marker = true;
            marked.Add(p);
            if (p.IsConst) {
                if (neg && p.Const!.Value.Sign > 0) {
                    neg = false;
                    if (!pos)
                        return 0;
                }
                else if (pos && p.Const!.Value.Sign < 0) {
                    pos = false;
                    if (!neg)
                        return 0;
                }
                continue;
            }
            Debug.Assert(p.Var is not null && p.Then is not null && p.Else is not null);
            stack.Push(p.Then);
            stack.Push(p.Else);
        }
        foreach (var m in marked) {
            Debug.Assert(m.Marker);
            m.Marker = false;
        }
        Debug.Assert(!(pos && neg));
        if (!pos && !neg)
            return 0;
        return pos ? 1 : -1;
    }

    [Pure]
    public int CompareTo(PDD<T>? other) {
        if (ReferenceEquals(this, other))
            return 0;
        if (ReferenceEquals(null, other))
            return 1;
        Debug.Assert(ReferenceEquals(Manager, other.Manager));
        if (IsConst && other.IsConst)
            return Const!.Value.CompareTo(other.Const!.Value);
        if (IsConst)
            return -1;
        if (other.IsConst)
            return 1;
        Debug.Assert(Var is not null && Then is not null && Else is not null);
        Debug.Assert(other.Var is not null && other.Then is not null && other.Else is not null);
        int cmp = Var.CompareTo(other.Var);
        if (cmp != 0)
            return cmp;
        cmp = Then.CompareTo(other.Then);
        if (cmp != 0)
            return cmp;
        return Else.CompareTo(other.Else);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public void CollectSymbols(NonTermSet nonTermSet, HashSet<CharToken> alphabet) =>
        CollectSymbols(this, nonTermSet, alphabet);

    public static void CollectSymbols(PDD<T> p, NonTermSet nonTermSet, HashSet<CharToken> alphabet) {
        Stack<PDD<T>> stack = [];
        List<PDD<T>> marked = [];
        Debug.Assert(!p.Marker);
        stack.Push(p);
        while (stack.Count > 0) {
            p = stack.Pop();
            if (p.Marker)
                continue;
            p.Marker = true;
            marked.Add(p);
            if (p.IsConst)
                continue;
            Debug.Assert(p.Var is not null && p.Then is not null && p.Else is not null);
            if (p.Var is IntVar iv)
                nonTermSet.Add(iv);
            stack.Push(p.Then);
            stack.Push(p.Else);
        }
        foreach (var m in marked) {
            Debug.Assert(m.Marker);
            m.Marker = false;
        }
    }

    [Pure]
    public static IntExpr ToExpr(Environment env, Dictionary<NamedStrToken, int> currentModificationCnt, PDD<BigInteger> p) {
        Context ctx = env.Ctx;
        if (p.IsConst) {
            try {
                return ctx.MkInt((long)p.Const!.Value);
            }
            catch (OverflowException) {
                return ctx.MkInt(p.Const!.Value.ToString());
            }
        }
        Debug.Assert(p.Var is not null && p.Then is not null && p.Else is not null);
        IntExpr thenExpr = ToExpr(env, currentModificationCnt, p.Then);
        IntExpr elseExpr = ToExpr(env, currentModificationCnt, p.Else);
        return (IntExpr)ctx.MkAdd(ctx.MkMul(p.Var.ToExpr(env, currentModificationCnt), thenExpr), elseExpr);
    }

    [Pure]
    public static (PDD<BigInteger> pos, PDD<BigInteger> neg) GetPosNeg(PDD<BigInteger> p) {
        if (p.IsConst) {
            int s = p.Const!.Value.Sign;
            if (s < 0)
                return (p.Manager.Zero, p.Manager.MkPDD(-p.Const.Value));
            if (s > 0)
                return (p.Manager.MkPDD(p.Const.Value), p.Manager.Zero);
            return (p.Manager.Zero, p.Manager.Zero);
        }
        Debug.Assert(p.Var is not null && p.Then is not null && p.Else is not null);
        var (pos1, neg1) = GetPosNeg(p.Then);
        var (pos2, neg2) = GetPosNeg(p.Else);
        return (p.Manager.MkPDD(p.Var, pos1, pos2), 
                p.Manager.MkPDD(p.Var, neg1, neg2));
    }

    public static Interval<BigInteger> GetBounds(NielsenNode node, IEnumerable<PDD<BigInteger>.Monomial> p) {
        var interval = new Interval<BigInteger>();
        foreach (var m in p) {
            Interval<BigInteger> subInterval = new(new InfNum<BigInteger>(m.Coefficient));
            foreach (var vt in m.Variables) {
                var varBounds = node.GetBounds(vt.Var);
                for (int i = 0; i < vt.Pow; i++) {
                    subInterval = subInterval.MergeMultiplication(varBounds);
                }
            }
            interval = interval.MergeAddition(subInterval);
            if (interval.IsFull)
                return interval;
        }
        return interval;
    }

    // the constant offset is necessarily the last entry
    void CollectTerms(in T c, List<PowerTerm> vars, List<Monomial> terms) {
        if (IsConst) {
            if (!T.IsZero(Const!.Value))
                terms.Add(new Monomial(c * Const!.Value, [..vars]));
            return;
        }

        Debug.Assert(Var is not null && Then is not null && Else is not null);
        bool inc = vars.Count > 0 && vars[^1].Var.Equals(Var);

        if (inc)
            vars[^1] = new PowerTerm(Var, vars[^1].Pow + 1);
        else
            vars.Add(new PowerTerm(Var, 1));

        Then.CollectTerms(in c, vars, terms);

        if (inc)
            vars[^1] = new PowerTerm(Var, vars[^1].Pow - 1);
        else
            vars.RemoveAt(vars.Count - 1);

        Else.CollectTerms(in c, vars, terms);
    }

    public List<Monomial> Monomials() {
        var (terms, offset) = MonomialDecomposition();
        if (!T.IsZero(offset))
            terms.Add(new Monomial(offset, []));
        return terms;
    }

    public (List<Monomial> monomials, T offset) MonomialDecomposition() {
        var terms = new List<Monomial>();
        CollectTerms(T.One, [], terms);
        if (terms.Count == 0 || terms[^1].Variables.Count != 0) 
            return (terms, T.Zero);
        var offset = terms[^1].Coefficient;
        terms.RemoveAt(terms.Count - 1);
        return (terms, offset);
    }

    public string ToExpandedString() {
        var terms = new List<Monomial>();
        CollectTerms(T.One, [], terms);
        if (terms.Count == 0)
            return "0";
        Debug.Assert(!T.IsZero(terms[^1].Coefficient));
        return string.Join(" + ", terms);
    }

    public string ToCompactString() {
        if (IsConst)
            return Const!.Value.ToString()!;

        Debug.Assert(Var is not null);
        Debug.Assert(Then is not null);
        Debug.Assert(Else is not null);

        string thenStr = Then.ToString();
        Debug.Assert(thenStr.Length > 0 && thenStr != "0");

        var sb = new StringBuilder();

        var varStr = Var.ToString();
        if (thenStr != "1")
            sb.Append(thenStr).Append('*');
        sb.Append(varStr);

        if (Else.IsZero)
            return sb.ToString();

        string elseStr = Else.ToString();
        Debug.Assert(elseStr.Length > 0 && elseStr != "0");
        return sb.Append(" + ").Append(elseStr).ToString();
    }

    public override string ToString() => 
        ToExpandedString();

    public readonly struct PowerTerm {
        public readonly NamedInt Var;
        public readonly uint Pow;

        public PowerTerm(NamedInt var, uint pow) {
            Debug.Assert(pow < 10);
            Var = var;
            Pow = pow;
        }

        public override bool Equals(object? obj) =>
            obj is PowerTerm p && Var.Equals(p.Var) && Pow == p.Pow;

        public override int GetHashCode() => HashCode.Combine(Var.GetHashCode(), Pow);

        public override string ToString() {
            return Pow switch {
                1 => Var.ToString(),
                < 10 => Var + "^" + Pow,
                _ => Var + "^{" + Pow + "}",
            };
        }
    }

    public readonly struct Monomial {
        public readonly T Coefficient;
        public readonly List<PowerTerm> Variables;

        public Monomial(T coefficient, List<PowerTerm> variables) {
            Debug.Assert(!T.IsZero(coefficient) || variables.Count == 0);
            Coefficient = coefficient;
            Variables = variables;
        }

        public PDD<T> ToPDD(PDDManager manager) {
            var res = manager.MkPDD(Coefficient);
            foreach (var vt in Variables) {
                var v = manager.MkPDD(vt.Var);
                for (int i = 0; i < vt.Pow; i++) {
                    res = Mul(res, v);
                }
            }
            return res;
        }

        public override string ToString() {
            if (Variables.Count == 0)
                return Coefficient.ToString() ?? "??";
            Debug.Assert(!T.IsZero(Coefficient));
            if (Coefficient.Equals(T.One))
                return string.Join("*", Variables);
            return Coefficient + " * " + string.Join("*", Variables);
        }
    }
}

static class PDDExtension {
    [MethodImpl(MethodImplOptions.AggressiveInlining), Pure]
    public static (PDD<BigInteger> pos, PDD<BigInteger> neg) GetPosNeg(this PDD<BigInteger> p) =>
        PDD<BigInteger>.GetPosNeg(p);

    [MethodImpl(MethodImplOptions.AggressiveInlining), Pure]
    public static IntExpr ToExpr(this PDD<BigInteger> p, Environment env, Dictionary<NamedStrToken, int> currentModificationCnt) =>
        PDD<BigInteger>.ToExpr(env, currentModificationCnt, p);

    [MethodImpl(MethodImplOptions.AggressiveInlining), Pure]
    public static Interval<BigInteger> GetBounds(this PDD<BigInteger> p, NielsenNode node) {
        var monomials = p.Monomials();
        return PDD<BigInteger>.GetBounds(node, monomials);
    }
}