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

    public Len(uint val) {
        this.val = val;
        IsInf = false;
    }

    public Len(BigInteger val) {
        this.val = val;
        IsInf = false;
    }

    public static implicit operator Len(int val) => new(val);
    public static implicit operator Len(uint val) => new(val);

    public static implicit operator Len(BigInteger val) => new(val);

    public bool TryGetInt(out int v) {
        v = 0;
        if (IsInf)
            return false;
        v = (int)val;
        // TODO: Check if it is larger than int.MaxValue or smaller than int.MinValue
        return true;
    }

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

    public static Len operator++(Len a) => a + 1;

    public static Len operator --(Len a) => a - 1;

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

    public (Len r, BigInteger m) DivRem(BigInteger d) {
        Debug.Assert(!IsZero || !d.IsZero);
        if (d.IsZero)
            return IsPos ? (PosInf, 0) : (NegInf, 0);
        if (IsInf)
            return IsPos == d.Sign > 0 ? (PosInf, 0) : (NegInf, 0);
        return IsZero 
            ? (0, 0) 
            : BigInteger.DivRem(val, d);
    }

    // Round towards 0
    public Len Div(Len b) {
        Debug.Assert(b != 0);
        Debug.Assert(!IsInf || !b.IsInf);

        if (IsZero) {
            Debug.Assert(!b.IsInf);
            return 0;
        }
        if (IsInf)
            return IsPos == b.IsPos ? PosInf : NegInf;
        return val / b.val;
    }

    public Len Abs() => IsNeg ? -this : this;

    public BigInteger GreatestCommonDivisor(Len t) {
        Debug.Assert(!IsInf);
        Debug.Assert(!t.IsInf);
        Debug.Assert(!IsZero);
        Debug.Assert(!t.IsZero);
        var gcd = BigInteger.GreatestCommonDivisor(val, t.val);
        Debug.Assert(gcd.Sign > 0);
        return gcd;
    }

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

    public static explicit operator int(Len v) {
        if (v.IsInf)
            throw new InvalidCastException("Cannot cast infinity to int");
        if (v.val.Sign > 0 && v.val > int.MaxValue)
            throw new OverflowException("Value is larger than int.MaxValue");
        if (v.val.Sign < 0 && v.val < int.MinValue)
            throw new OverflowException("Value is smaller than int.MinValue");
        return (int)v.val;
    }

    public static explicit operator BigInteger(Len v) {
        if (v.IsInf)
            throw new InvalidCastException("Cannot cast infinity to int");
        return v.val;
    }

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