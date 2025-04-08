using Microsoft.Z3;
using StringBreaker.Constraints;
using StringBreaker.Strings.Tokens;

namespace StringBreaker.Strings;

public class StrTokenRef : IComparable<StrTokenRef> {

    public StrToken Token { get; }
    public int CopyIdx { get; }

    public StrTokenRef(StrToken token, int copyIdx) {
        Token = token;
        CopyIdx = copyIdx;
    }

    public StrRef? ResolveTo(NielsenContext ctx) {
        Check if CopyIdx has to be rewritten by ctx
        return Token.Resolve(CopyIdx);
    }

    public override bool Equals(object? obj) =>
        obj is StrTokenRef other && Equals(other);

    public bool Equals(StrTokenRef other) =>
        Token.Equals(other.Token) && CopyIdx == other.CopyIdx;

    public override int GetHashCode() =>
        HashCode.Combine(Token, CopyIdx);

    public Expr ToExpr(NielsenContext ctx) {
        StrRef? r = ResolveTo(ctx);
        return r is null ? Token.ToExpr(CopyIdx, ctx) : r.ToExpr(ctx);
    }

    public int CompareTo(StrTokenRef? other) {
        if (ReferenceEquals(this, other))
            return 0;
        if (other is null)
            return 1;
        int cmp = Token.CompareTo(other.Token);
        if (cmp != 0)
            return cmp;
        return CopyIdx.CompareTo(other.CopyIdx);
    }

    public override string ToString() => Token + "#" + CopyIdx;
}