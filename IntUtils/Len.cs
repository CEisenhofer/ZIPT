using System.Diagnostics;
using System.Numerics;
using Microsoft.Z3;
using StringBreaker.Constraints;

namespace StringBreaker.IntUtils;

public readonly struct Len : IComparable<Len> {

    readonly BigInteger val;
    public bool IsInf { get; } = false;
    public bool IsPos => val.Sign > 0;
    public bool IsNeg => val.Sign < 0;
    public bool IsZero => val.Sign == 0;
    public bool IsPosInf => IsInf && IsPos;
    public bool IsNegInf => IsInf && IsNeg;

    public static readonly Len PosInf = new(true, true);
    public static readonly Len NegInf = new(true, false);
    public static readonly Len Zero = new(0);

    Len(bool inf, bool pos) {
        IsInf = inf;
        val = pos ? BigInteger.One : BigInteger.MinusOne;
    }

    public Len(int val) {
        this.val = val;
        IsInf = false;
    }

    public Len(BigInteger val) {
        this.val = val;
        IsInf = false;
    }

    public static implicit operator Len(int val) => new(val);

    public static implicit operator Len(BigInteger val) => new(val);

    public static Len operator -(Len a) {
        if (a.IsInf)
            return a.IsPos ? NegInf : PosInf;
        return -a.val;
    }

    public static Len operator +(Len a, Len b) {
        if (a.IsPosInf || b.IsPosInf) {
            Debug.Assert(!a.IsNegInf && !b.IsNegInf);
            return PosInf;
        }
        if (a.IsNegInf || b.IsNegInf) {
            Debug.Assert(!a.IsPosInf && !b.IsPosInf);
            return NegInf;
        }
        Debug.Assert(!a.IsInf && !b.IsInf);
        return a.val + b.val;
    }

    public static Len operator -(Len a, Len b) {
        Debug.Assert(!(a.IsPosInf && b.IsPosInf));
        Debug.Assert(!(a.IsNegInf && b.IsNegInf));
        if (a.IsPosInf && b.IsNegInf)
            return PosInf;
        if (a.IsNegInf && b.IsPosInf)
            return NegInf;
        if (a.IsPosInf && b.IsNegInf)
            return PosInf;
        Debug.Assert(!a.IsInf && !b.IsInf);
        return a.val - b.val;
    }

    public static Len operator *(Len a, Len b) {
        if (a.IsZero || b.IsZero)
            // Mathematically problematically, but in this case it makes sense
            return 0;
        Debug.Assert(!a.IsPosInf || !b.IsNegInf);
        Debug.Assert(!a.IsNegInf || !b.IsPosInf);

        if (a.IsInf || b.IsInf)
            return a.IsPos == b.IsPos ? PosInf : NegInf;

        return a.val * b.val;
    }

    public void DivMod(Len b, out Len div, out Len mod) {
        Debug.Assert(b != 0);
        if (this == 0) {
            div = mod = 0;
            return;
        }
        Debug.Assert(!IsInf && !b.IsInf);
        div = BigInteger.DivRem(val, b.val, out BigInteger rem);
        mod = rem;
    }

    public Len Abs() => IsNeg ? -this : this;

    public static Len Min(Len a, Len b) => a < b ? a : b;
    public static Len Max(Len a, Len b) => a > b ? a : b;

    public static bool operator ==(Len left, Len right) => left.CompareTo(right) == 0;

    public static bool operator !=(Len left, Len right) => left.CompareTo(right) != 0;

    public static bool operator <(Len left, Len right) =>
        left.CompareTo(right) < 0;

    public static bool operator >(Len left, Len right) =>
        left.CompareTo(right) > 0;

    public static bool operator <=(Len left, Len right) =>
        left.CompareTo(right) <= 0;

    public static bool operator >=(Len left, Len right) =>
        left.CompareTo(right) >= 0;

    public override bool Equals(object? obj) =>
        obj is Len len && Equals(len);

    public bool Equals(Len other) =>
        CompareTo(other) == 0;

    public int CompareTo(Len other) {
        int cmp = val.Sign.CompareTo(other.val.Sign);
        if (cmp != 0)
            return cmp;
        if (IsInf && other.IsInf)
            return 0;
        if (IsPosInf || other.IsNegInf)
            return 1;
        if (IsNegInf || other.IsPosInf)
            return -1;
        Debug.Assert(!IsInf || !other.IsInf);
        return val.CompareTo(other.val);
    }

    public override int GetHashCode() => 430783571 * IsInf.GetHashCode() + 593872421 * val.GetHashCode();

    public IntExpr ToExpr(NielsenGraph graph) {
        Debug.Assert(!IsInf);
        return graph.Ctx.MkInt(val.ToString());
    }

    public override string ToString() => IsPosInf
        ? "∞"
        : IsNegInf
            ? "-∞"
            : val.ToString();
}