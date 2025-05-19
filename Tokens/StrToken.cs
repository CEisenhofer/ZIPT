using System.Diagnostics;
using Microsoft.Z3;
using ZIPT.Constraints;
using ZIPT.Constraints.ConstraintElement;
using ZIPT.Tokens.AuxTokens;

namespace ZIPT.Tokens;

public abstract class StrToken : IEquatable<StrToken>, IComparable<StrToken> {

    public abstract bool Ground { get; }
    public abstract bool IsNullable(NielsenNode node);

    public abstract Str Apply(Subst subst);
    public abstract Str Apply(Interpretation itp);
    public abstract List<(Str str, List<IntConstraint> sideConstraints, Subst? varDecomp)> GetPrefixes(bool dir);
    public abstract Expr ToExpr(NielsenGraph graph);

    public abstract bool RecursiveIn(NamedStrToken v);

    public override bool Equals(object? other) =>
        other is StrToken token && Equals(token);

    // The order is important! The lower one will be used as root in the e-graph
    public static readonly Dictionary<Type, int> StrTokenOrder = new() {
        { typeof(PowerToken), 0 },
        { typeof(SymCharToken), 1 },
        { typeof(CharToken), 2 },
        { typeof(StrVarToken), 3 },
        { typeof(StrAtToken), 4 },
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

    public abstract bool Equals(StrToken? other);
    public abstract override int GetHashCode();

    public sealed override string ToString() => ToString(null);
    public abstract string ToString(NielsenGraph? graph);

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
            if (graph.Cache.IsLen(e.FuncDecl))
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