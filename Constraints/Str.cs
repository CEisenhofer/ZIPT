using System.Diagnostics;
using Microsoft.Z3;
using StringBreaker.Constraints.ConstraintElement;
using StringBreaker.MiscUtils;
using StringBreaker.Tokens;

namespace StringBreaker.Constraints;

public class Str : IndexedQueue<StrToken>, IComparable<Str> {

    public Str() { }

    public Str(StrToken tokens) : base([tokens]) { }
    public Str(ICollection<StrToken> tokens) : base(tokens) { }
    public Str(params StrToken[] tokens) : base(tokens) { }
    public bool Ground => this.All(token => token.Ground);
    public bool IsNullable(NielsenNode node) => this.All(token => token.IsNullable(node));

    public bool RecursiveIn(StrVarToken item) => this.Any(o => o.RecursiveIn(item));

    public Str Apply(Subst subst) {
        Str result = [];
        foreach (var token in this) {
            result.AddLastRange(token.Apply(subst));
        }
        return result;
    }

    public Str Apply(Interpretation subst) {
        Str result = [];
        foreach (var token in this) {
            result.AddLastRange(token.Apply(subst));
        }
        return result;
    }

    public Str ApplyFirst(StrVarToken v, Str repl) {
        bool found = false;
        Str result = [];
        foreach (var token in this) {
            if (!found && token.Equals(v)) {
                result.AddLastRange(repl);
                found = true;
                continue;
            }
            result.Add(token);
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

    // Proper prefixes
    public List<(Str str, List<IntConstraint> sideConstraints, Subst? varDecomp)> GetPrefixes() {
        // P(u_1...u_n) := P(u_1) | u_1 P(u_2) | ... | u_1...u_{n-1} P(u_n)
        List<(Str str, List<IntConstraint> sideConstraints, Subst varDecomp)> ret = [];
        Str prefix = [];
        List<IntConstraint> cnstrs = [];
        for (int i = 0; i < Count; i++) {
            var current = this[i].GetPrefixes();
            for (int j = 0; j < current.Count; j++) {
                current[j].str.AddFirstRange(prefix);
                current[j].sideConstraints.AddRange(cnstrs);
            }
            ret.AddRange(current);
            prefix.Add(this[i]);
            cnstrs.AddRange(current[^1].sideConstraints);
        }
        return ret;
    }

    public Expr ToExpr(NielsenGraph graph) {
        if (Count == 0)
            return graph.Propagator.Epsilon;
        Expr last = this[^1].ToExpr(graph);
        for (int i = Count - 1; i > 0; i--) {
            last = graph.Propagator.ConcatFct.Apply(this[i - 1].ToExpr(graph), last);
        }
        return last;
    }

    public void CollectSymbols(HashSet<StrVarToken> vars, HashSet<CharToken> alphabet) {
        foreach (var token in this) {
            switch (token) {
                case StrVarToken v:
                    vars.Add(v);
                    break;
                case CharToken c:
                    alphabet.Add(c);
                    break;
                case PowerToken p:
                    p.Base.CollectSymbols(vars, alphabet);
                    p.Power.CollectSymbols(vars, alphabet);
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

    public bool EqualsRotation(int pos, Str s) {
        Debug.Assert(pos >= 0 && pos <= Count);
        if (Count != s.Count)
            return false;
        if (pos == 0)
            return Equals(s);
        int len = Count - pos;
        for (int i = 0; i < len; i++) {
            if (!this[i].Equals(s[pos + i]))
                return false;
        }
        for (int i = len; i < Count; i++) {
            if (!this[i].Equals(s[i - len]))
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

    public MSet<StrToken> ToSet() => new(this);

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