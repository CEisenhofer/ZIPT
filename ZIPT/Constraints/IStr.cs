using Microsoft.Z3;
using System.Diagnostics;
using System.Text;
using ZIPT.MiscUtils;
using ZIPT.Tokens;

namespace ZIPT.Constraints;

public interface IStr : IEquatable<IStr>, IComparable<IStr> {

    public StrToken this[int index] { get; }
    public IReadOnlyDictionary<NamedStrToken, uint> ContainedVariables { get; }
    public uint Length { get; }
    public bool Ground { get; }
    public bool Word { get; }

    public IEnumerable<StrToken> GetTokens();
    public IEnumerable<StrToken> GetTokensRev();

    public bool IsEmpty() => Length == 0;
    public bool IsNonEmpty() => Length != 0;

    // TODO: Improve
    public bool IsNullable(NielsenNode node) => GetTokens().All(token => token.IsNullable(node));

    public StrToken Peek() => Peek(true);
    public StrToken Peek(bool dir);
    public StrToken Peek(bool dir, int idx);

    public IStr Drop(uint left, uint right);

    public Expr ToExpr(NielsenGraph graph) {
        if (IsEmpty())
            return graph.Env.Epsilon;
        using var e = GetTokensRev().GetEnumerator();
        if (!e.MoveNext()) {
            Debug.Assert(false);
            return graph.Env.Epsilon;
        }
        Expr last = e.Current.ToExpr(graph);
        while (e.MoveNext()) {
            last = graph.Env.MkConcat(e.Current.ToExpr(graph), last);
        }
        return last;
    }
    public static NonTermSet CollectSymbols(params IStr[] strings) {
        NonTermSet nonTermSet = new();
        foreach (IStr s in strings) {
            s.CollectSymbols(nonTermSet, []);
        }
        return nonTermSet;
    }

    public void CollectSymbols(NonTermSet nonTermSet, HashSet<CharToken> alphabet) {
        foreach (var token in GetTokens()) {
            switch (token) {
                case NamedStrToken v:
                    nonTermSet.Add(v);
                    break;
                case CharToken c:
                    alphabet.Add(c);
                    break;
                case SymCharToken s:
                    nonTermSet.Add(s);
                    break;
                case PowerToken p:
                    p.Base.CollectSymbols(nonTermSet, alphabet);
                    p.Power.CollectSymbols(nonTermSet, alphabet);
                    break;
                default:
                    throw new NotSupportedException();
            }
        }
    }

    int IComparable<IStr>.CompareTo(IStr? other) {
        if (other is null)
            return 1;
        if (ReferenceEquals(this, other))
            return 0;

        if (Length != other.Length)
            return Length.CompareTo(other.Length);
        using var enumerator = GetTokens().GetEnumerator();
        using var otherEnumerator = other.GetTokens().GetEnumerator();
        while (enumerator.MoveNext() && otherEnumerator.MoveNext()) {
            int cmp = enumerator.Current.CompareTo(otherEnumerator.Current);
            if (cmp != 0)
                return cmp;
        }
        return 0;
    }

    bool IEquatable<IStr>.Equals(IStr? other) {
        if (other is null)
            return false;
        if (Length != other.Length)
            return false;
        if (ReferenceEquals(this, other))
            return true;

        Debug.Assert(!ReferenceEquals(other, this));
        using var enumerator = GetTokens().GetEnumerator();
        using var otherEnumerator = other.GetTokens().GetEnumerator();
        while (enumerator.MoveNext() && otherEnumerator.MoveNext()) {
            if (!enumerator.Current.Equals(otherEnumerator.Current))
                return false;
        }
        Debug.Assert(GetHashCode() == other.GetHashCode());
        Debug.Assert(ContainedVariables.EqualContent(other.ContainedVariables));
        return true;
    }

    public string ToString() {
        if (Length == 0)
            return "ε";
        StringBuilder sb = new();
        foreach (StrToken token in GetTokens()) {
            sb.Append(token);
        }
        return sb.ToString();
    }
}