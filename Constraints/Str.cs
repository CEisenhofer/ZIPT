using System.Collections.Specialized;
using System.Diagnostics;
using Microsoft.Z3;
using ZIPT.Constraints.ConstraintElement;
using ZIPT.IntUtils;
using ZIPT.MiscUtils;
using ZIPT.Tokens;

namespace ZIPT.Constraints;

public class Str : IndexedQueue<StrToken>, IComparable<Str> {

    public Str() { }

    public Str(int capacity) : base(capacity) { }
    public Str(StrToken tokens) : base([tokens]) { }
    public Str(ICollection<StrToken> tokens) : base(tokens) { }
    public Str(params StrToken[] tokens) : base(tokens) { }
    public bool Ground => this.All(token => token.Ground);
    public bool IsNullable(NielsenNode node) => this.All(token => token.IsNullable(node));

    public bool RecursiveIn(NamedStrToken item) => this.Any(o => o.RecursiveIn(item));

    public Str Apply(Subst subst) {
        Str result = [];
        foreach (var token in this) {
            result.AddLastRange(token.Apply(subst));
        }
        return result;
    }

    public Str Apply(Interpretation itp) {
        Str result = [];
        foreach (var token in this) {
            result.AddLastRange(token.Apply(itp));
        }
        return result;
    }

    public Str ApplyLast(StrVarToken v, Str repl) {
        bool found = false;
        Str result = [];
        foreach (var token in this.Reverse()) {
            if (!found && token.Equals(v)) {
                result.AddFirstRange(repl.Reverse().ToList());
                found = true;
                continue;
            }
            result.AddFirst(token);
        }
        return new Str(result.Reverse().ToList());
    }

    public Str Rotate(int idx) {
        Debug.Assert(idx >= 0 && idx < Count);
        if (idx == 0)
            return Clone();
        Str result = new Str(Count);
        for (int i = idx; i < Count; i++) {
            result.AddLast(this[i]);
        }
        for (int i = 0; i < idx; i++) {
            result.AddLast(this[i]);
        }
        return result;
    }

    // Proper prefixes
    public List<(Str str, List<IntConstraint> sideConstraints, Subst? varDecomp)> GetPrefixes(bool dir) {
        // P(u_1...u_n) := P(u_1) | u_1 P(u_2) | ... | u_1...u_{n-1} P(u_n)
        List<(Str str, List<IntConstraint> sideConstraints, Subst? varDecomp)> ret = [];
        Str prefix = [];
        for (int i = 0; i < Count; i++) {
            var current = Peek(dir, i).GetPrefixes(dir);
            for (int j = 0; j < current.Count; j++) {
                current[j].str.AddRange(prefix, dir);
            }
            ret.AddRange(current);
            prefix.Add(Peek(dir, i), !dir);
        }
        return ret;
    }

    public Expr ToExpr(NielsenGraph graph) {
        if (Count == 0)
            return graph.Cache.Epsilon;
        Expr last = this[^1].ToExpr(graph);
        for (int i = Count - 1; i > 0; i--) {
            last = graph.Cache.MkConcat(this[i - 1].ToExpr(graph), last);
        }
        return last;
    }

    public void CollectSymbols(NonTermSet nonTermSet, HashSet<CharToken> alphabet) {
        foreach (var token in this) {
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

    public static Str operator +(Str lhs, Str rhs) {
        Str result = new(lhs);
        result.AddLastRange(rhs);
        return result;
    }

    public override bool Equals(object? obj) =>
        obj is Str other && Equals(other);

    public bool Equals(Str other) =>
        Count == other.Count && this.SequenceEqual(other);

    // Compare if this[shift:]this[:shift] == other
    public bool RotationEquals(Str other, int shift) {
        Debug.Assert(shift > 0 && shift < other.Count);
        if (Count != other.Count)
            return false;
#if DEBUG
        if (Count != 2 || shift != 1) {
            ;
            // Console.WriteLine("Debug stop");
        }
#endif
        int to = Count - shift;
        for (int i = 0; i < to; i++) {
            if (!this[i + shift].Equals(other[i]))
                return false;
        }
        for (int i = to; i < Count; i++) {
            if (!this[i - to].Equals(other[i]))
                return false;
        }
        return true;
    }

    public override int GetHashCode() => 
        this.Aggregate(387815837, (current, token) => current * 941706509 + token.GetHashCode());

    public StrToken? First() => Count > 0 ? PeekFirst() : null;
    public StrToken? Last() => Count > 0 ? PeekLast() : null;

    public override string ToString() => Count == 0 ? "ε" : string.Concat(this);

    public string ToString(NielsenGraph? graph) => 
        Count == 0 ? "ε" : string.Concat(this.Select(o => o.ToString(graph)));

    public StrToken Peek(bool dir) =>
        dir ? PeekFirst() : PeekLast();

    public StrToken Peek(bool dir, int pos) =>
        dir ? this[pos] : this[^(pos + 1)];

    public void Drop(bool dir) {
        if (dir)
            PopFirst();
        else
            PopLast();
    }

    public void DropFirst() => PopFirst();
    public void DropLast() => PopLast();

    public MSet<StrToken, BigInt> ToSet() => new(this);

    public Str Clone() => new(this);

    public int CompareTo(Str? other) {
        if (other is null || Count > other.Count)
            return 1;
        if (Count < other.Count)
            return -1;
        for (int i = 0; i < Count; i++) {
            switch (this[i].CompareTo(other[i])) {
                case < 0:
                    return -1;
                case > 0:
                    return 1;
            }
        }
        return 0;
    }
}