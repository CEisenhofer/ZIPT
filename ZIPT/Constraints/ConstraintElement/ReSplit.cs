using Microsoft.Z3;
using System.Diagnostics;
using System.Text;
using ZIPT.Constraints.Modifier;
using ZIPT.IntUtils;
using ZIPT.Strings.Chunks;
using ZIPT.Strings.Tokens;
using ZIPT.Strings.Tokens.RegexTokens;

namespace ZIPT.Constraints.ConstraintElement;

// xu \in r might have been split into
// 1) x \in prefix
// 2) u \in postfix
// 3) prefix + postfix = r
// 4) prefix \notin blocked[i] for any i
// This class represents 3 and 4
// Statements like u + prefix + postfix = r or prefix + u + postfix = r are not representable
public class ReSplit : StrConstraint {

    public Str Regex { get; set; }
    public PreToken Prefix { get; set; }
    public PostToken Postfix { get; set; }
    List<Str> Blocked { get; } = [];

    public IReadOnlyList<Str> BlockedList => Blocked;

    public bool IsPropagating { get; }

    public ReSplit(Str regex, PreToken prefix, PostToken postfix) {
        Regex = regex;
        Prefix = prefix;
        Postfix = postfix;
    }

    public ReSplit(Str regex, PreToken prefix, PostToken postfix, List<Str>? blocked, bool isPropagating) {
        Regex = regex;
        Prefix = prefix;
        Postfix = postfix;
        if (blocked is not null)
            Blocked.AddRange(blocked);
        IsPropagating = isPropagating;
    }

    public override Constraint Apply(Subst subst, NielsenNode node) {
        // always forward evaluation
        Debug.Assert(!subst.Var.Equals(Postfix));
        var newRegex = node.Env.StrManager.Subst(Regex, subst);
        bool isPropagating = IsPropagating;
        if (subst.Var.Equals(Prefix)) {
            if (subst.Str.IsEmpty())
                isPropagating = true;
            else {
                // assume for now, we have prefix / u prefix
                Debug.Assert(subst.Str.Last.Equals(Prefix));
                // As we assume that prefix/postfix ONLY occur here and in one other regex membership constraint
                // and that the substitution resulted from here, we just derive it and it has to work
                // hence, we ignore substitutions in which we assign kleene stars [we only assign kleene stars or characters]
                Debug.Assert((subst.Str is { Length: 2, First: KleeneToken }) ||
                             subst.Str.GetEnumerator().SkipLast(1).All(o => o is CharToken));
                if (subst.Str.First is not KleeneToken) {
                    for (int i = 0; i < subst.Str.Length - 1; i++) {
                        CharToken c = (CharToken)subst.Str[i];
                        newRegex = newRegex.Derivative(node.Env, c, true);
                    }
                }
            }
        }
        if (isPropagating == IsPropagating && ReferenceEquals(Regex, newRegex))
            return this;
        return new ReSplit(newRegex, Prefix, Postfix, Blocked.ToList(), isPropagating);
    }

    public override Constraint Apply(CharSubst subst, NielsenNode node) {
        var newRegex = node.Env.StrManager.Subst(node.Env, Regex, subst);
        return ReferenceEquals(Regex, newRegex)
            ? this
            : new ReSplit(newRegex, Prefix, Postfix, Blocked.ToList(), IsPropagating);
    }

    public override ReSplit Apply(Interpretation itp) {
        // always forward evaluation
        Debug.Assert(!itp.Substitution.ContainsKey(Postfix));
        var newRegex = itp.Env.StrManager.Subst(Regex, itp);
        bool isPropagating = IsPropagating;
        if (itp.Substitution.TryGetValue(Prefix, out var subst)) {
            if (subst.Str.IsEmpty())
                isPropagating = true;
            // assume for now, we have prefix / u prefix
            Debug.Assert(subst.Str.Last.Equals(Prefix));
            // As we assume that prefix/postfix ONLY occur here and in one other regex membership constraint
            // and that the substitution resulted from here, we just derive it and it has to work
            // hence, we ignore substitutions in which we assign kleene stars [we only assign kleene stars or characters]
            Debug.Assert((subst.Str is { Length: 2, First: KleeneToken }) || subst.Str.GetEnumerator().SkipLast(1).All(o => o is CharToken));
            if (subst.Str.First is not KleeneToken) {
                for (int i = 0; i < subst.Str.Length - 1; i++) {
                    CharToken c = (CharToken)subst.Str[i];
                    newRegex = newRegex.Derivative(itp.Env, c, true);
                }
            }
        }
        if (isPropagating == IsPropagating && ReferenceEquals(Regex, newRegex))
            return this;
        return new ReSplit(newRegex, Prefix, Postfix, Blocked.ToList(), isPropagating);
    }

    protected override SimplifyResult SimplifyAndPropagateInternal(NielsenNode node, DetModifier sConstr, ref BacktrackReasons reason) {
        if (IsPropagating) {
            if (sConstr.Add(new Subst(Postfix, Regex)) == SimplifyResult.Proceed)
                return SimplifyResult.RestartAndSatisfied;
            return SimplifyResult.Restart;
        }
        return SimplifyResult.Proceed;
    }

    public override BoolExpr ToExpr(NielsenGraph graph) =>
        graph.Env.Ctx.MkEq(
            graph.Env.ConcatFct.Apply(Prefix.ToExpr(graph), Postfix.ToExpr(graph)),
            Regex.ToExpr(graph)
        );

    public override void CollectSymbols(NonTermSet nonTermSet, HashSet<CharToken> alphabet) {
        Regex.CollectSymbols(nonTermSet, alphabet);
        Prefix.CollectSymbols(nonTermSet, alphabet);
        Postfix.CollectSymbols(nonTermSet, alphabet);
        // do not add the blocked ones
    }

    public override Constraint Negate() => 
        // this would not make sense [internally created constraint]
        throw new NotSupportedException();

    public override bool Contains(NamedStrToken namedStrToken) => 
        Prefix.Equals(namedStrToken) || Postfix.Equals(namedStrToken) || Regex.ContainsVar(namedStrToken);

    public override ModifierBase Extend(NielsenNode node, Dictionary<NamedInt, PDD<BigRational>> intSubst) {
        Debug.Assert(!IsPropagating);
        return new RegexSplitModifier(Prefix, Regex.FirstMinTerms(), true);
    }

    public override int CompareToInternal(StrConstraint other) {
        if (ReferenceEquals(this, other))
            return 0;
        ReSplit o = (ReSplit)other;
        int cmp = Regex.CompareTo(o.Regex);
        if (cmp != 0)
            return cmp;
        cmp = Blocked.Count.CompareTo(o.Blocked.Count);
        if (cmp != 0)
            return cmp;
        for (int i = 0; i < Blocked.Count; i++) {
            cmp = Blocked[i].CompareTo(o.Blocked[i]);
            if (cmp != 0)
                return cmp;
        }
        cmp = Prefix.CompareTo(o.Prefix);
        if (cmp != 0)
            return cmp;
        Debug.Assert(Postfix.CompareTo(o.Postfix) == 0);
        return 0;
    }


    public override bool Equals(object? obj) => obj is ReSplit other && Equals(other);
    public bool Equals(ReSplit? other) => other is not null && GetType() == other.GetType() && CompareTo(other) == 0;

    public override int GetHashCode() => 
        HashCode.Combine(Prefix.GetHashCode(), Postfix.GetHashCode()) * 886358197;

    public override string ToString() {
        if (IsPropagating)
            return $"{Postfix} = {Regex}";
        StringBuilder sb = new();
        sb.Append(Prefix).Append(';').Append(Postfix).Append(" = ").Append(Regex);
        foreach (var b in Blocked) {
            sb.Append("; ").Append(Prefix).Append(" != ").Append(b).Append(".*");
        }
        return sb.ToString();
    }

}