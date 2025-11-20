using Microsoft.Z3;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using ZIPT.Constraints;
using ZIPT.Constraints.ConstraintElement.AuxConstraints;
using ZIPT.MiscUtils;
using ZIPT.Strings.Chunks;
using ZIPT.Strings.Tokens.AuxTokens;
using ZIPT.Strings.Tokens.RegexTokens;

namespace ZIPT.Strings.Tokens;

public abstract class StrToken : IEquatable<StrToken>, IComparable<StrToken> {

    public abstract bool Ground { get; }
    public abstract bool RegexFree { get; }
    public abstract bool Derivable { get; }
    public abstract bool Nullable { get; }
    public abstract bool BasicRegex { get; }

    public abstract List<StrDecomposition> GetDecomposition(NielsenNode node, bool fwd);

    public abstract Expr ToExpr(Environment env, Dictionary<NamedStrToken, int> currentModificationCnt);

    public override bool Equals(object? other) =>
        other is StrToken token && Equals(token);

    // The order is important! The lower one will be used as root in the e-graph
    public static readonly Dictionary<Type, int> StrTokenOrder = new() {
        { typeof(FailToken), 0 },
        { typeof(PowerToken), 1 },
        { typeof(CharToken), 2 },
        { typeof(StrVarToken), 3 },
        { typeof(StrAtToken), 4 },
        { typeof(NotToken), 5 },
        { typeof(KleeneToken), 6 },
        { typeof(UnionToken), 7 },
        { typeof(IntersectToken), 8 },
        { typeof(LoopToken), 9 },
        { typeof(SetToken), 10 }, // deliberately last, as for merging those for intersection (MkUnion) can easily add them as last
    };

    public int CompareTo(StrToken? other) {
        if (other is null)
            return 1;
        if (GetType() == other.GetType())
            return CompareToInternal(other);
        int val1 = StrTokenOrder[GetType()];
        int val2 = StrTokenOrder[other.GetType()];
        Debug.Assert(val1 != val2);
        return val1.CompareTo(val2);
    }

    protected abstract int CompareToInternal(StrToken other);
    public abstract void CollectSymbols(NonTermSet nonTermSet, CharacterSet alphabet);

    [Pure]
    public virtual MinTerms FirstMinTerms() => throw new NotSupportedException();
    [Pure]
    public virtual MinTerms LastMinTerms() => throw new NotSupportedException();

    public abstract bool Equals(StrToken? other);
    public abstract override int GetHashCode();
    public virtual Str OptSimplify(StrManager manager) => manager.Single(this);

    public sealed override string ToString() => ToString(null);
    public abstract string ToString(NielsenGraph? graph);

    public Str Derivative(Environment env, CharToken set, bool fwd) =>
        Derivative(env, new CharacterSet(new CharacterRange(set.Value)), fwd);

    public virtual Str Derivative(Environment env, CharacterSet set, bool fwd) => throw new NotSupportedException();

    public static string ExprToStr(NielsenGraph? graph, Expr e) {
        if (e.IsTrue)
            return "true";
        if (e.IsFalse)
            return "false";
        if (e.IsAnd)
            return $"({string.Join(" & ", e.Args.Select(o => ExprToStr(graph, o)))})";
        if (e.IsOr)
            return $"({string.Join(" | ", e.Args.Select(o => ExprToStr(graph, o)))})";
        if (e.IsImplies)
            return $"({ExprToStr(graph, e.Arg(0))} => {ExprToStr(graph, e.Arg(1))})";
        if (e.IsNot)
            return $"!({ExprToStr(graph, e.Args[0])})";
        if (e is IntNum num)
            return num.ToString();
        if (e.IsAdd)
            return $"({string.Join(" + ", e.Args.Select(o => ExprToStr(graph, o)))})";
        if (e.IsSub)
            return $"({string.Join(" - ", e.Args.Select(o => ExprToStr(graph, o)))})";
        if (e.IsMul)
            return $"({string.Join(" * ", e.Args.Select(o => ExprToStr(graph, o)))})";
        if (e.IsIDiv)
            return $"({ExprToStr(graph, e.Arg(0))} / {ExprToStr(graph, e.Arg(1))})";
        if (e.IsModulus)
            return $"({ExprToStr(graph, e.Arg(0))} % {ExprToStr(graph, e.Arg(1))})";
        if (e.IsEq)
            return $"({ExprToStr(graph, e.Arg(0))} = {ExprToStr(graph, e.Arg(1))})";
        if (e.IsGT)
            return $"({ExprToStr(graph, e.Arg(0))} > {ExprToStr(graph, e.Arg(1))})";
        if (e.IsGE)
            return $"({ExprToStr(graph, e.Arg(0))} \u2265 {ExprToStr(graph, e.Arg(1))})";
        if (e.IsLT)
            return $"({ExprToStr(graph, e.Arg(0))} < {ExprToStr(graph, e.Arg(1))})";
        if (e.IsLE)
            return $"({ExprToStr(graph, e.Arg(0))} \u2264 {ExprToStr(graph, e.Arg(1))})";
        if (graph is not null) {
            if (graph.Env.IsLen(e.FuncDecl))
                return $"|[{ExprToStr(graph, e.Args[0])}]|";
            var s = graph.TryParseStr(e);
            if (s is not null)
                return s.ToString(graph);
        }
        if (!e.IsApp) 
            return e.ToString();
        if (e.NumArgs == 0) 
            return e.ToString();
        return e.FuncDecl.Name + "(" + string.Join(", ", e.Args.Select(o => ExprToStr(graph, o))) + ")";
    }
}