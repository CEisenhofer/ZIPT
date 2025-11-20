using Microsoft.Z3;
using System.Diagnostics;
using System.Text;
using ZIPT.Constraints;
using ZIPT.MiscUtils;
using ZIPT.Strings.Chunks;

namespace ZIPT.Strings.Tokens.RegexTokens;

public sealed class LoopToken : StrToken {

    public uint Min { get; }
    public uint Max { get; }
    public Str Base { get; }

    public override bool Ground => Base.Ground;
    public override bool RegexFree => false;
    public override bool Derivable => true;
    public override bool Nullable => Min == 0;
    public override bool BasicRegex { get; }

    public LoopToken(Str @base, uint min, uint max) {
        Base = @base;
        Min = min;
        Max = max;
        BasicRegex = @base.BasicRegex;
        Debug.Assert(!@base.Nullable || min == 0);
        Debug.Assert(min <= max);
    }

    public override List<StrDecomposition> GetDecomposition(NielsenNode node, bool fwd) => 
        throw new NotSupportedException();

    public override Expr ToExpr(Environment env, Dictionary<NamedStrToken, int> currentModificationCnt) {
        var e = Base.ToExpr(env, currentModificationCnt);
        return env.MkLoopExpr(e, Min, Max);
    }

    protected override int CompareToInternal(StrToken other) {
        LoopToken otherM = (LoopToken)other;
        int cmp = Base.CompareTo(otherM.Base);
        if (cmp != 0)
            return cmp;
        cmp = Min.CompareTo(otherM.Min);
        return cmp != 0 ? cmp : Max.CompareTo(otherM.Max);
    }

    public override void CollectSymbols(NonTermSet nonTermSet, CharacterSet alphabet) => 
        Base.CollectSymbols(nonTermSet, alphabet);

    public override MinTerms FirstMinTerms() => Base.FirstMinTerms();

    public override MinTerms LastMinTerms() => Base.LastMinTerms();

    public override bool Equals(StrToken? other) => 
        other is LoopToken l && Base.Equals(l.Base) && Min == l.Min && Max == l.Max;

    public override int GetHashCode() =>
        770109551 * HashCode.Combine(Base, Min, Max);

    public override string ToString(NielsenGraph? graph) {
        StringBuilder sb = new();
        void AppendRange() {
            if (Min == Max)
                sb.Append('{').Append(Min).Append('}');
            else if (Min == 0)
                sb.Append("{;").Append(Max).Append('}');
            else
                sb.Append('{').Append(Min).Append(';').Append(Max).Append('}');

        }
        string s = Base.ToString();
        if (Base.Length > 1)
            sb.Append('(').Append(s).Append(')');
        else
            sb.Append(s);
        AppendRange();
        return sb.ToString();
    }

    public override Str Derivative(Environment env, CharacterSet set, bool fwd) {
        var der = Base.Derivative(env, set, fwd);
        if (Min == 0)
            return env.StrManager.Concat(der, env.StrManager.MkLoop(Base, 0, Max - 1));
        return env.StrManager.Concat(der, env.StrManager.MkLoop(Base, Min - 1, Max - 1));
    }

}