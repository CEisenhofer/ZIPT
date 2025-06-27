using System.Diagnostics;
using System.Numerics;

namespace ZIPT.IntUtils;

public readonly struct BigIntInf : IComparable<BigIntInf> {

    readonly BigInteger val;
    public bool IsInf { get; } = false;
    public bool IsPos => val.Sign > 0;
    public bool IsNeg => val.Sign < 0;
    public bool IsOne => !IsInf && val.IsOne;
    public bool IsZero => val.Sign == 0;
    public bool IsPosInf => IsInf && IsPos;
    public bool IsNegInf => IsInf && IsNeg;

    public static readonly BigIntInf PosInf = new(true, true);
    public static readonly BigIntInf NegInf = new(true, false);

    BigIntInf(bool inf, bool pos) {
        IsInf = inf;
        val = pos ? BigInteger.One : BigInteger.MinusOne;
    }

    public BigIntInf(int val) {
        this.val = val;
        IsInf = false;
    }

    public BigIntInf(uint val) {
        this.val = val;
        IsInf = false;
    }

    public BigIntInf(BigInteger val) {
        this.val = val;
        IsInf = false;
    }

    public static implicit operator BigIntInf(int val) => new(val);
    public static implicit operator BigIntInf(uint val) => new(val);

    public static implicit operator BigIntInf(BigInteger val) => new(val);

    public bool TryGetInt(out int v) {
        v = 0;
        if (IsInf)
            return false;
        if (val < int.MinValue || val > int.MaxValue)
            return false;
        v = (int)val;
        return true;
    }

    public static BigIntInf operator -(BigIntInf a) {
        if (a.IsInf)
            return a.IsPos ? NegInf : PosInf;
        return -a.val;
    }

    public static BigIntInf operator +(BigIntInf a, BigIntInf b) {
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

    public static BigIntInf operator -(BigIntInf a, BigIntInf b) {
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

    public static BigIntInf operator++(BigIntInf a) => a + 1;

    public static BigIntInf operator --(BigIntInf a) => a - 1;

    public static BigIntInf operator *(BigIntInf a, BigIntInf b) {
        if (a.IsZero || b.IsZero)
            // Mathematically problematically, but in this case it makes sense
            return 0;
        Debug.Assert(!a.IsPosInf || !b.IsNegInf);
        Debug.Assert(!a.IsNegInf || !b.IsPosInf);

        if (a.IsInf || b.IsInf)
            return a.IsPos == b.IsPos ? PosInf : NegInf;

        return a.val * b.val;
    }

    // Round towards 0
    public BigIntInf Div(BigIntInf b) {
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

    public static BigIntInf Min(BigIntInf a, BigIntInf b) => a < b ? a : b;
    public static BigIntInf Max(BigIntInf a, BigIntInf b) => a > b ? a : b;

    public BigIntInf Abs() => IsNeg ? -this : this;

    public static bool operator ==(BigIntInf left, BigIntInf right) => left.CompareTo(right) == 0;

    public static bool operator !=(BigIntInf left, BigIntInf right) => left.CompareTo(right) != 0;

    public static bool operator <(BigIntInf left, BigIntInf right) =>
        left.CompareTo(right) < 0;

    public static bool operator >(BigIntInf left, BigIntInf right) =>
        left.CompareTo(right) > 0;

    public static bool operator <=(BigIntInf left, BigIntInf right) =>
        left.CompareTo(right) <= 0;

    public static bool operator >=(BigIntInf left, BigIntInf right) =>
        left.CompareTo(right) >= 0;

    public static explicit operator int(BigIntInf v) {
        if (v.IsInf)
            throw new InvalidCastException("Cannot cast infinity to int");
        if (v.val.Sign > 0 && v.val > int.MaxValue)
            throw new OverflowException("Value is larger than int.MaxValue");
        if (v.val.Sign < 0 && v.val < int.MinValue)
            throw new OverflowException("Value is smaller than int.MinValue");
        return (int)v.val;
    }

    public static explicit operator BigInteger(BigIntInf v) {
        if (v.IsInf)
            throw new InvalidCastException("Cannot cast infinity to int");
        return v.val;
    }

    public static explicit operator BigInt(BigIntInf v) {
        if (v.IsInf)
            throw new InvalidCastException("Cannot cast infinity to int");
        return new BigInt(v.val);
    }

    public override bool Equals(object? obj) =>
        obj is BigIntInf len && Equals(len);

    public bool Equals(BigIntInf other) =>
        CompareTo(other) == 0;

    public int CompareTo(BigIntInf other) {
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

    public override string ToString() => IsPosInf
        ? "∞"
        : IsNegInf
            ? "-∞"
            : val.ToString();
}