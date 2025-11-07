using Microsoft.Z3;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.Text;
using ZIPT.Constraints;
using ZIPT.MiscUtils;
using ZIPT.Strings.Chunks;

namespace ZIPT.Strings.Tokens.RegexTokens;

public sealed class IntersectToken : StrToken {

    public IReadOnlyList<Str> Cases { get; }

    public override bool Ground { get; }
    public override bool RegexFree => false;
    public override bool Derivable => true;
    public override bool Nullable { get; }
    public override bool BasicRegex => false;

    MinTerms? firstMinTerm;
    MinTerms? lastMinTerm;

    public IntersectToken(IReadOnlyList<Str> cases) {
        Debug.Assert(cases.Count > 1);
        Debug.Assert(cases.SkipLast(1).Zip(cases.Skip(1)).All(o => o.First.CompareTo(o.Second) < 0));
        Debug.Assert(cases.All(o => o is not SingletonStr { StrToken: IntersectToken }));
        Cases = cases;
        Ground = true;
        Nullable = true;
        foreach (var r in cases) {
            Ground &= r.Ground;
            Nullable &= r.Nullable;
        }
    }

    public override List<StrDecomposition> GetDecomposition(NielsenNode node, bool fwd) {
        throw new NotImplementedException();
    }

    public override Expr ToExpr(NielsenGraph graph) {
        Debug.Assert(Cases.Count > 1);
        Expr expr = Cases[^1].ToExpr(graph);
        for (int i = Cases.Count - 1; i > 0; i--) {
            var e = Cases[i - 1].ToExpr(graph);
            expr = graph.Env.InterFct.Apply(e, expr);
        }
        return expr;
    }

    protected override int CompareToInternal(StrToken other) {
        IntersectToken inter = (IntersectToken)other;
        int cmp = Cases.Count.CompareTo(inter.Cases.Count);
        if (cmp != 0)
            return cmp;
        for (int i = 0; i < Cases.Count; i++) {
            cmp = Cases[i].CompareTo(inter.Cases[i]);
            if (cmp != 0)
                return cmp;
        }
        return 0;
    }

    public override void CollectSymbols(NonTermSet nonTermSet, HashSet<CharToken> alphabet) {
        foreach (var @case in Cases) {
            @case.CollectSymbols(nonTermSet, alphabet);
        }
    }

    public override MinTerms FirstMinTerms() {
        if (firstMinTerm is not null)
            return firstMinTerm;
        firstMinTerm = new MinTerms();
        foreach (var @case in Cases) {
            firstMinTerm = firstMinTerm.Merge(@case.FirstMinTerms());
        }
        return firstMinTerm;
    }

    public override MinTerms LastMinTerms() {
        if (lastMinTerm is not null)
            return lastMinTerm;
        lastMinTerm = new MinTerms();
        foreach (var @case in Cases) {
            lastMinTerm = lastMinTerm.Merge(@case.LastMinTerms());
        }
        return lastMinTerm;
    }

    public override bool Equals(StrToken? other) {
        if (other is not IntersectToken inter || Cases.Count != inter.Cases.Count)
            return false;
        for (int i = 0; i < Cases.Count; i++) {
            if (!Cases[i].Equals(inter.Cases[i]))
                return false;
        }
        return true;
    }

    public override int GetHashCode() =>
        Cases.Aggregate(481063813, (h, o) => h + 533023987 * o.GetHashCode());

    public override string ToString(NielsenGraph? graph) {
        StringBuilder sb = new();
        sb.Append('(');
        for (int i = 0; i < Cases.Count; i++) {
            if (i > 0)
                sb.Append('&');
            string s = Cases[i].ToString(graph);
            if (s.Length == 1)
                sb.Append(s);
            else
                sb.Append('(').Append(s).Append(')');
        }
        sb.Append(')');
        return sb.ToString();
    }

    public override Str Derivative(Environment env, CharacterSet set, bool fwd) {
        Debug.Assert(Cases.Count > 1);
        var derivatives = new List<Str>(Cases.Count);
        for (var i = 0; i < Cases.Count; i++) {
            derivatives.Add(Cases[i].Derivative(env, set, fwd));
        }
        return env.StrManager.MkIntersection(derivatives);
    }
}