using System.Numerics;
using Microsoft.Z3;
using ZIPT.Constraints;
using ZIPT.IntUtils;
using ZIPT.Strings.Chunks;

namespace ZIPT.Strings.Tokens.AuxTokens;

public sealed class StrAtToken : NamedStrToken {

    public Str S { get; }
    public PDD<BigInteger> I { get; }

    public override string OriginalName => $"strAt({S},{I})";

    public StrAtToken(Str s, PDD<BigInteger> i) {
        S = s;
        I = i;
    }

    public override StrAtToken GetExtension1() => (StrAtToken)(Extension1 ??= new StrAtToken(S, I));
    public override StrAtToken GetExtension2() => (StrAtToken)(Extension2 ??= new StrAtToken(S, I));

    public override Expr ToExpr(Environment env, Dictionary<NamedStrToken, int> currentModificationCnt) {
        Expr? e = env.GetCachedStrExpr(this, currentModificationCnt);
        if (e is not null)
            return e;
        e = env.StrAtFct.Apply(S.ToExpr(env, currentModificationCnt), I.ToExpr(env, currentModificationCnt));
        env.SetCachedExpr(this, e, currentModificationCnt);
        return e;
    }
}