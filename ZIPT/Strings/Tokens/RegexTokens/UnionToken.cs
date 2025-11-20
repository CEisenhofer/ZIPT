using Microsoft.Z3;
using System.Diagnostics;
using System.Text;
using ZIPT.Constraints;
using ZIPT.MiscUtils;
using ZIPT.Strings.Chunks;

namespace ZIPT.Strings.Tokens.RegexTokens;

public sealed class UnionToken : StrToken {

    public IReadOnlyList<Str> Cases { get; }

    public override bool Ground { get; }
    public override bool RegexFree => false;
    public override bool Derivable => true;
    public override bool Nullable { get; }
    public override bool BasicRegex { get; }

    MinTerms? firstMinTerm;
    MinTerms? lastMinTerm;

    public UnionToken(IReadOnlyList<Str> cases) {
        Debug.Assert(cases.Count > 1);
        Debug.Assert(cases.SkipLast(1).Zip(cases.Skip(1)).All(o => o.First.CompareTo(o.Second) < 0));
        Debug.Assert(cases.All(o => o is not SingletonStr { StrToken: UnionToken }));
        Cases = cases;
        Ground = true;
        Nullable = false;
        BasicRegex = true;
        foreach (var r in cases) {
            Ground &= r.Ground;
            Nullable |= r.Nullable;
            BasicRegex &= r.BasicRegex;
        }
    }

    public UnionToken(params Str[] cases) : this((IReadOnlyList<Str>)cases) { }

    public override List<StrDecomposition> GetDecomposition(NielsenNode node, bool fwd) => 
        throw new NotSupportedException();

    public override Expr ToExpr(Environment env, Dictionary<NamedStrToken, int> currentModificationCnt) {
        /*Expr[] exprs = new Expr[Cases.Length];
        for (int i = 0; i < Cases.Length; i++) {
            var e = Cases[i].ToExpr(graph);
            exprs[i] = System e as ReExpr ?? graph.Ctx.MkToRe((SeqExpr)e);
        }
        return graph.Ctx.MkUnion(exprs);*/
        Debug.Assert(Cases.Count > 1);
        Expr expr = Cases[^1].ToExpr(env, currentModificationCnt);
        for (int i = Cases.Count - 1; i > 0; i--) {
            var e = Cases[i - 1].ToExpr(env, currentModificationCnt);
            expr = env.UnionFct.Apply(e, expr);
        }
        return expr;
    }

    protected override int CompareToInternal(StrToken other) {
        UnionToken union = (UnionToken)other;
        int cmp = Cases.Count.CompareTo(union.Cases.Count);
        if (cmp != 0)
            return cmp;
        for (int i = 0; i < Cases.Count; i++) {
            cmp = Cases[i].CompareTo(union.Cases[i]);
            if (cmp != 0)
                return cmp;
        }
        return 0;
    }

    public override void CollectSymbols(NonTermSet nonTermSet, CharacterSet alphabet) {
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
        if (other is not UnionToken union || Cases.Count != union.Cases.Count)
            return false;
        for (int i = 0; i < Cases.Count; i++) {
            if (!Cases[i].Equals(union.Cases[i]))
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
                sb.Append('|');
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
        List<Str> derivatives = new(Cases.Count);
        foreach (var @case in Cases) {
            derivatives.Add(@case.Derivative(env, set, fwd));
        }
        return env.StrManager.MkUnion(derivatives);
    }

}