using System.Diagnostics;
using System.Diagnostics.CodeAnalysis;
using System.Diagnostics.Contracts;
using System.Numerics;
using System.Runtime.CompilerServices;
using System.Text;
using Microsoft.Z3;
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

        PDDManager() {
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

        public PDD<T> VarPDD(IntVar v) =>
            MkPDD(v, One, Zero);

    }

    public PDDManager Manager { get; }
    // TODO: IdSet?

    public bool Marker { get; set; }
    public NamedInt? Var { get; }
    public PDD<T>? Then { get; }
    public PDD<T>? Else { get; }
    public T? Const { get; }

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
            while (!c.IsConst()) {
                c = c.Then!; // skip to the next branch
            }
            Debug.Assert(c.Const.HasValue);
            Debug.Assert(!T.IsZero(c.Const.Value));
            return T.IsPositive(c.Const.Value);
        }
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining), Pure]
    public bool IsConst() => Const.HasValue;

    [MethodImpl(MethodImplOptions.AggressiveInlining), Pure]
    public bool IsConst(out T val) {
        val = default;
        if (IsConst())
            return false;
        val = Const!.Value;
        return true;
    }

    PDD(NamedInt var, PDD<T> thenBranch, PDD<T> elseBranch) {
        Log.Caller(nameof(Manager.MkPDD));
        Debug.Assert(!ReferenceEquals(thenBranch.Manager, elseBranch.Manager));
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

    public bool IsZero => IsConst() && Const!.Value.Equals(T.Zero);
    public bool IsOne => IsConst() && Const!.Value.Equals(T.One);


    [MethodImpl(MethodImplOptions.AggressiveInlining), Pure]
    public PDD<T> Add(PDD<T> b) => Add(this, b);

    [Pure]
    public static PDD<T> Add(PDD<T> a, PDD<T> b) {
        Debug.Assert(ReferenceEquals(a.Manager, b.Manager));
        PDDManager m = a.Manager;
        if (a.IsConst() && b.IsConst())
            return m.MkPDD(a.Const!.Value + b.Const!.Value);

        if (a == b)
            return Mul(m.Two, a);
        if (a.IsZero)
            return b;
        if (b.IsZero)
            return a;

        if (a.IsConst())
            return Add(b, a); // Const on the right

        Debug.Assert(a.Var is not null && a.Then is not null && a.Else is not null);

        if (b.IsConst())
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
    public static PDD<T> Negate(PDD<T> p) {
        if (p.IsConst())
            return p.Manager.MkPDD(-p.Const!.Value);
        return p.Manager.MkPDD(p.Var!, Negate(p.Then!), Negate(p.Else!));
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining), Pure]
    public PDD<T> Mul(PDD<T> b) => Mul(this, b);

    [Pure]
    public static PDD<T> Mul(PDD<T> a, PDD<T> b) {
        Debug.Assert(ReferenceEquals(a.Manager, b.Manager));
        PDDManager m = a.Manager;
        if (a.IsConst() && b.IsConst())
            return m.MkPDD(a.Const!.Value * b.Const!.Value);

        if (a.IsZero || b.IsZero)
            return m.Zero;
        if (a.IsConst())
            return Mul(b, a);

        Debug.Assert(a.Var is not null && a.Then is not null && a.Else is not null);

        if (b.IsConst())
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

    [MethodImpl(MethodImplOptions.AggressiveInlining), Pure]
    public PDD<T> Substitute(IntVar targetVar, PDD<T> replacement) =>
        Substitute(this, targetVar, replacement);

    [Pure]
    public static PDD<T> Substitute(PDD<T> p, IntVar targetVar, PDD<T> replacement) {
        if (p.IsConst())
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
            if (p.IsConst()) {
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
        if (IsConst() && other.IsConst())
            return Const!.Value.CompareTo(other.Const!.Value);
        if (IsConst())
            return -1;
        if (other.IsConst())
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
            if (p.IsConst())
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
    public static IntExpr ToExpr(NielsenGraph graph, PDD<BigInteger> p) {
        Context ctx = graph.Env.Ctx;
        if (p.IsConst()) {
            try {
                return ctx.MkInt((long)p.Const!.Value);
            }
            catch (OverflowException) {
                return ctx.MkInt(p.Const!.Value.ToString());
            }
        }
        Debug.Assert(p.Var is not null && p.Then is not null && p.Else is not null);
        IntExpr thenExpr = ToExpr(graph, p.Then);
        IntExpr elseExpr = ToExpr(graph, p.Else);
        return (IntExpr)ctx.MkAdd(ctx.MkMul(p.Var.ToExpr(graph), thenExpr), elseExpr);
    }

    [Pure]
    public static (PDD<BigInteger> pos, PDD<BigInteger> neg) GetPosNeg(PDD<BigInteger> p) {
        if (p.IsConst()) {
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

    public static Interval GetBounds(NielsenNode node, PDD<BigInteger> p) {
        if (p.IsConst()) {
            BigInteger val = p.Const!.Value;
            return new Interval(val, val);
        }
        // TODO: Cache sub-results
        Debug.Assert(p.Var is not null && p.Then is not null && p.Else is not null);
        var thenBounds = GetBounds(node, p.Then);
        var elseBounds = GetBounds(node, p.Else);
        var bounds = thenBounds.MergeAddition(elseBounds);
        if (node.IntBounds.TryGetValue(p.Var, out var varBounds)) {
            p.Var.GetBounds
        }
        bounds.MergeMultiplication(p.Var);
        return bounds;
    }

    void CollectTerms(in T c, List<(NamedInt v, uint pow)> vars, List<(T c, List<(NamedInt v, uint pow)> vars)> terms) {
        if (IsConst()) {
            terms.Add((c * Const!.Value, [..vars]));
            return;
        }

        Debug.Assert(Var is not null && Then is not null && Else is not null);
        bool inc = vars.Count > 0 && vars[^1].v.Equals(Var);

        if (inc)
            vars[^1] = (Var, vars[^1].pow + 1);
        else
            vars.Add((Var, 1));

        Then.CollectTerms(in c, vars, terms);

        if (inc)
            vars[^1] = (Var, vars[^1].pow - 1);
        else
            vars.RemoveAt(vars.Count - 1);

        Else.CollectTerms(in c, vars, terms);
    }

    public string ToExpandedString() {
        var terms = new List<(T c, List<(NamedInt v, uint pow)> vars)>();
        CollectTerms(T.One, [], terms);
        
        return string.Join(" + ", terms.Select(t =>
        {
            StringBuilder sb = new();
            Debug.Assert(!T.IsZero(t.c));
            if (t.c != T.One)
                sb.Append(t.c);
            if (t.vars.Count == 0)
                return sb.ToString();
            return sb.Append("*").Append(string.Join("*", t.vars.Select(v =>
            {
                Debug.Assert(v.pow > 0);
                if (v.pow == 1)
                    return v.v.ToString();
                string s = v.pow.ToString();
                Debug.Assert(s.Length > 0);
                return s.Length == 1 ? $"{v.v}^{s}" : $"{v.v}^{{{s}}}";
            }))).ToString();
        }));
    }

    public string ToCompactString() {
        if (IsConst())
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
}

static class PDDExtension {
    [MethodImpl(MethodImplOptions.AggressiveInlining), Pure]
    public static (PDD<BigInteger> pos, PDD<BigInteger> neg) GetPosNeg(this PDD<BigInteger> p) =>
        PDD<BigInteger>.GetPosNeg(p);

    [MethodImpl(MethodImplOptions.AggressiveInlining), Pure]
    public static IntExpr ToExpr(this PDD<BigInteger> p, NielsenGraph graph) =>
        PDD<BigInteger>.ToExpr(graph, p);

    [MethodImpl(MethodImplOptions.AggressiveInlining), Pure]
    public static Interval GetBounds(this PDD<BigInteger> p, NielsenNode node) =>
        PDD<BigInteger>.GetBounds(node, p);
}