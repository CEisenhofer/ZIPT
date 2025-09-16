using System.Diagnostics;
using System.Numerics;

namespace ZIPT.IntUtils;

public readonly struct InfNum<T> : IComparable<InfNum<T>> where T : INumberBase<T>, IComparable<T> {

    readonly T val;
    public bool IsInf { get; } = false;
    public bool IsPos => T.IsPositive(val);
    public bool IsNeg => T.IsNegative(val);
    public bool IsOne => !IsInf && val.Equals(T.One);
    public bool IsZero => T.IsZero(val);
    public bool IsPosInf => IsInf && IsPos;
    public bool IsNegInf => IsInf && IsNeg;

    public static readonly InfNum<T> PosInfNum = new(true, true);
    public static readonly InfNum<T> NegInfNum = new(true, false);

    public static readonly InfNum<T> Zero = new(T.Zero);
    public static readonly InfNum<T> One = new(T.One);
    public static readonly InfNum<T> MinusOne = Zero - One;

    InfNum(bool inf, bool pos) {
        IsInf = inf;
        val = pos ? T.One : -T.One;
    }

    public InfNum(T val) {
        this.val = val;
        IsInf = false;
    }

    public static implicit operator InfNum<T>(T val) => new(val);

    public static bool TryGetInt(in InfNum<BigInteger> num, out int v) {
        v = 0;
        if (num.IsInf)
            return false;
        if (num.val < int.MinValue || num.val > int.MaxValue)
            return false;
        v = (int)num.val;
        return true;
    }

    public static InfNum<T> operator -(InfNum<T> a) {
        if (a.IsInf)
            return a.IsPos ? NegInfNum : PosInfNum;
        return -a.val;
    }

    public static InfNum<T> operator +(InfNum<T> a, InfNum<T> b) {
        if (a.IsPosInf || b.IsPosInf) {
            Debug.Assert(!a.IsNegInf && !b.IsNegInf);
            return PosInfNum;
        }
        if (a.IsNegInf || b.IsNegInf) {
            Debug.Assert(!a.IsPosInf && !b.IsPosInf);
            return NegInfNum;
        }
        Debug.Assert(!a.IsInf && !b.IsInf);
        return a.val + b.val;
    }

    public static InfNum<T> operator -(InfNum<T> a, InfNum<T> b) {
        Debug.Assert(!(a.IsPosInf && b.IsPosInf));
        Debug.Assert(!(a.IsNegInf && b.IsNegInf));
        if (a.IsPosInf && b.IsNegInf)
            return PosInfNum;
        if (a.IsNegInf && b.IsPosInf)
            return NegInfNum;
        if (a.IsPosInf && b.IsNegInf)
            return PosInfNum;
        Debug.Assert(!a.IsInf && !b.IsInf);
        return a.val - b.val;
    }

    public static InfNum<T> operator++(InfNum<T> a) => a + One;

    public static InfNum<T> operator --(InfNum<T> a) => a - One;

    public static InfNum<T> operator *(InfNum<T> a, InfNum<T> b) {
        if (a.IsZero || b.IsZero)
            // Mathematically problematically, but in this case it makes sense
            return T.Zero;
        Debug.Assert(!a.IsPosInf || !b.IsNegInf);
        Debug.Assert(!a.IsNegInf || !b.IsPosInf);

        if (a.IsInf || b.IsInf)
            return a.IsPos == b.IsPos ? PosInfNum : NegInfNum;

        return a.val * b.val;
    }

    // Round towards 0
    public InfNum<T> Div(InfNum<T> b) {
        Debug.Assert(!T.IsZero(b.val));
        Debug.Assert(!IsInf || !b.IsInf);

        if (IsZero) {
            Debug.Assert(!b.IsInf);
            return T.Zero;
        }
        if (IsInf)
            return IsPos == b.IsPos ? PosInfNum : NegInfNum;
        return val / b.val;
    }

    public InfNum<T> Div(T b) {
        Debug.Assert(!T.IsZero(b));

        if (IsZero)
            return T.Zero;
        if (IsInf)
            return IsPos == T.IsPositive(b) ? PosInfNum : NegInfNum;
        return val / b;
    }

    public static InfNum<T> Min(InfNum<T> a, InfNum<T> b) => a < b ? a : b;
    public static InfNum<T> Max(InfNum<T> a, InfNum<T> b) => a > b ? a : b;

    public InfNum<T> Abs() => IsNeg ? -this : this;

    public static bool operator ==(InfNum<T> left, InfNum<T> right) => left.CompareTo(right) == 0;

    public static bool operator !=(InfNum<T> left, InfNum<T> right) => left.CompareTo(right) != 0;

    public static bool operator <(InfNum<T> left, InfNum<T> right) =>
        left.CompareTo(right) < 0;

    public static bool operator >(InfNum<T> left, InfNum<T> right) =>
        left.CompareTo(right) > 0;

    public static bool operator <=(InfNum<T> left, InfNum<T> right) =>
        left.CompareTo(right) <= 0;

    public static bool operator >=(InfNum<T> left, InfNum<T> right) =>
        left.CompareTo(right) >= 0;

    public static explicit operator T(InfNum<T> v) {
        if (v.IsInf)
            throw new InvalidCastException("Cannot cast infinity to integer");
        return v.val;
    }

    public override bool Equals(object? obj) =>
        obj is InfNum<T> len && Equals(len);

    public bool Equals(InfNum<T> other) =>
        CompareTo(other) == 0;

    public static int Sign(in T val) =>
            T.IsZero(val) ? 0 : (T.IsPositive(val) ? 1 : -1);

    public int CompareTo(InfNum<T> other) {
        int cmp = Sign(val).CompareTo(Sign(other.val));
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

    public override string ToString() => 
        IsPosInf
        ? "∞"
        : IsNegInf
            ? "-∞"
            : val.ToString()!;
}