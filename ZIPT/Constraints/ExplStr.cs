using System.Diagnostics;
using Microsoft.Z3;
using ZIPT.Constraints.ConstraintElement;
using ZIPT.IntUtils;
using ZIPT.MiscUtils;
using ZIPT.Tokens;

namespace ZIPT.Constraints;

public class ExplStr : IndexedQueue<StrToken>, IStr {

    public ExplStr() { }

    public ExplStr(int capacity) : base(capacity) { }
    public ExplStr(StrToken tokens) : base([tokens]) { }
    public ExplStr(IReadOnlyList<StrToken> tokens) : base(tokens.ToList()) { }
    public ExplStr(ICollection<StrToken> tokens) : base(tokens) { }
    public ExplStr(params StrToken[] tokens) : base(tokens) { }

    public bool Ground => this.All(token => token.Ground);
    public bool Word => this.All(token => token is CharToken); // Word => Ground

    Dictionary<NamedStrToken, uint>? containedVars;

    public IReadOnlyDictionary<NamedStrToken, uint> ContainedVariables
    {
        get
        {
            if (containedVars is null)
                UpdateContained();
            Debug.Assert(containedVars is not null);
            return containedVars;
        }
    }

    public uint Length => (uint)Count;

    void UpdateContained() {
        Debug.Assert(containedVars is null);
        containedVars = [];
        foreach (var token in this) {
            if (token is not NamedStrToken namedToken) 
                continue;
            containedVars.Inc(namedToken);
        }
    }

    public ExplStr Apply(Subst subst) {
        ExplStr result = [];
        foreach (var token in this) {
            result.AddLastRange(token.Apply(subst));
        }
        return result;
    }

    public ExplStr Apply(Interpretation itp) {
        ExplStr result = [];
        foreach (var token in this) {
            result.AddLastRange(token.Apply(itp));
        }
        return result;
    }

    public ExplStr ApplyLast(StrVarToken v, ExplStr repl) {
        bool found = false;
        ExplStr result = [];
        foreach (var token in this.Reverse()) {
            if (!found && token.Equals(v)) {
                result.AddFirstRange(repl.Reverse().ToList());
                found = true;
                continue;
            }
            result.AddFirst(token);
        }
        return new ExplStr(result.Reverse().ToList());
    }

    public ExplStr Rotate(int idx) {
        Debug.Assert(idx >= 0 && idx < Count);
        if (idx == 0)
            return Clone();
        ExplStr result = new ExplStr(Count);
        for (int i = idx; i < Count; i++) {
            result.AddLast(this[i]);
        }
        for (int i = 0; i < idx; i++) {
            result.AddLast(this[i]);
        }
        return result;
    }

    public ExplStr SubStr(int start, int len) {
        Debug.Assert(0 <= start && 0 <= len && start + len <= Count);
        if (len == 0)
            return [];
        ExplStr s = new(len);
        for (int i = start; i < start + len; i++) {
            s.AddLast(this[i]);
        }
        return s;
    }

    // Proper prefixes
    public List<(ExplStr str, List<IntConstraint> sideConstraints, Subst? varDecomp)> GetPrefixes(bool dir) {
        // P(u_1...u_n) := P(u_1) | u_1 P(u_2) | ... | u_1...u_{n-1} P(u_n)
        List<(ExplStr str, List<IntConstraint> sideConstraints, Subst? varDecomp)> ret = [];
        ExplStr prefix = [];
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

    public IEnumerable<StrToken> GetTokens() => this;

    public IEnumerable<StrToken> GetTokensRev() {
        for (int i = Count; i > 0; i--) {
            yield return this[i - 1];
        }
    }

    public static ExplStr operator +(ExplStr lhs, ExplStr rhs) {
        ExplStr result = new(lhs);
        result.AddLastRange(rhs);
        return result;
    }

    public override bool Equals(object? obj) =>
        obj is IStr other && ((IStr)this).Equals(other);

    // Compare if this[shift:]this[:shift] == other
    public bool RotationEquals(ExplStr other, int shift) {
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

    public StrToken Peek(bool dir) =>
        dir ? PeekFirst() : PeekLast();

    public StrToken Peek(bool dir, int pos) =>
        dir ? this[pos] : this[^(pos + 1)];

    public ExplStr Drop(uint left, uint right) {
        if (left + right > Count)
            return [];
        ExplStr result = new((int)(Count - left - right));
        uint to = (uint)Count - right;
        for (uint i = left; i < to; i++) {
            result.AddLast(this[(int)i]);
        }
        return result;
    }

    public void Drop(bool dir) {
        if (dir)
            PopFirst();
        else
            PopLast();
    }

    public void DropFirst() => PopFirst();
    public void DropLast() => PopLast();

    public MSet<StrToken, BigInt> ToSet() => new(this);

    public ExplStr Clone() => new(this);

    public int CompareTo(IStr? other) {
        if (other is null)
            return 1;
        if (ReferenceEquals(this, other))
            return 0;

        if (Count != other.Length)
            return Count.CompareTo(other.Length);

        using var enumerator = GetTokens().GetEnumerator();
        using var otherEnumerator = other.GetTokens().GetEnumerator();
        while (enumerator.MoveNext() && otherEnumerator.MoveNext()) {
            int cmp = enumerator.Current.CompareTo(otherEnumerator.Current);
            if (cmp != 0)
                return cmp;
        }
        return 0;
    }
}