using System.Numerics;
using Microsoft.Z3;
using ZIPT.Constraints;
using ZIPT.IntUtils;
using ZIPT.Strings.Chunks;

namespace ZIPT.Strings.Tokens.AuxTokens;

public sealed class SubStrToken : NamedStrToken {

    public Str S { get; }
    public PDD<BigInteger> From { get; }
    public PDD<BigInteger> Len { get; }

    public override string OriginalName => $"subStr({S},{From},{Len})";

    public SubStrToken(Str s, PDD<BigInteger> from, PDD<BigInteger> len) {
        S = s;
        From = from;
        Len = len;
    }

    public override SubStrToken GetExtension1() => (SubStrToken)(Extension1 ??= new SubStrToken(S, From, Len));
    public override SubStrToken GetExtension2() => (SubStrToken)(Extension2 ??= new SubStrToken(S, From, Len));

    public override Expr ToExpr(Environment env, Dictionary<NamedStrToken, int> currentModificationCnt) {
        Expr? e = env.GetCachedStrExpr(this, currentModificationCnt);
        if (e is not null)
            return e;
        e = env.StrAtFct.Apply(S.ToExpr(env, currentModificationCnt), From.ToExpr(env, currentModificationCnt), Len.ToExpr(env, currentModificationCnt));
        env.SetCachedExpr(this, e, currentModificationCnt);
        return e;
    }
}