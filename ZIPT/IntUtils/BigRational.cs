using System.Diagnostics;
using System.Globalization;
using System.Numerics;

namespace ZIPT.IntUtils;

public readonly struct BigRational : INumberBase<BigRational>, IComparable<BigRational> {

    readonly BigInteger num;
    readonly BigInteger denum;

    public bool IsZero => num.IsZero;
    public bool IsPos => num.Sign > 0;
    public bool IsNeg => num.Sign < 0;
    public bool IsOne => num.IsOne && denum.IsOne;
    public bool IsMinusOne => (-this).IsOne;
    public bool IsInt => denum.IsOne;
    public static int Radix => 2;
    public static BigRational AdditiveIdentity => Zero;
    public static BigRational MultiplicativeIdentity => One;


    public static BigRational Parse(string s, IFormatProvider? provider) =>
        throw new NotSupportedException();
    public static bool TryParse(string? s, IFormatProvider? provider, out BigRational result) =>
        throw new NotSupportedException();
    public bool TryFormat(Span<char> destination, out int charsWritten, ReadOnlySpan<char> format, IFormatProvider? provider) =>
        throw new NotSupportedException();
    public static BigRational Parse(ReadOnlySpan<char> s, IFormatProvider? provider) =>
        throw new NotSupportedException();
    public static bool TryParse(ReadOnlySpan<char> s, IFormatProvider? provider, out BigRational result) =>
        throw new NotSupportedException();
    public static BigRational operator --(BigRational value) => value - One;
    public static BigRational operator ++(BigRational value) => value + One;
    public static BigRational operator +(BigRational value) => value;
    public static BigRational Abs(BigRational value) => value.Abs();
    public static bool IsCanonical(BigRational value) => true;
    public static bool IsComplexNumber(BigRational value) => false;
    public static bool IsEvenInteger(BigRational value) => value is { IsInt: true, num.IsEven: true };
    public static bool IsOddInteger(BigRational value) => value is { IsInt: true, num.IsEven: false };
    public static bool IsFinite(BigRational value) => true;
    public static bool IsImaginaryNumber(BigRational value) => false;
    public static bool IsInfinity(BigRational value) => false;
    public static bool IsInteger(BigRational value) => value.IsInt;
    public static bool IsNaN(BigRational value) => false;
    public static bool IsNegative(BigRational value) => value.IsNeg;
    public static bool IsPositive(BigRational value) => value.IsPos;
    public static bool IsNegativeInfinity(BigRational value) => false;
    public static bool IsPositiveInfinity(BigRational value) => false;
    public static bool IsNormal(BigRational value) => true;
    public static bool IsRealNumber(BigRational value) => true;
    public static bool IsSubnormal(BigRational value) => false;
    static bool INumberBase<BigRational>.IsZero(BigRational value) => value.IsZero;
    public static BigRational MaxMagnitude(BigRational x, BigRational y) {
        var ax = Abs(x);
        var ay = Abs(y);
        if (ax > ay)
            return x;
        if (ax == ay)
            return IsNegative(x) ? y : x;
        return y;
    }
    public static BigRational MaxMagnitudeNumber(BigRational x, BigRational y) => MaxMagnitude(x, y);
    public static BigRational MinMagnitude(BigRational x, BigRational y) {
        var ax = Abs(x);
        var ay = Abs(y);
        if (ax < ay)
            return x;
        if (ax == ay)
            return IsNegative(x) ? x : y;
        return y;
    }
    public static BigRational MinMagnitudeNumber(BigRational x, BigRational y) => MinMagnitude(x, y);
    public static BigRational Parse(ReadOnlySpan<char> s, NumberStyles style, IFormatProvider? provider) =>
        throw new NotSupportedException();
    public static BigRational Parse(string s, NumberStyles style, IFormatProvider? provider) =>
        throw new NotSupportedException();
    public static bool TryConvertFromChecked<TOther>(TOther value, out BigRational result) where TOther : INumberBase<TOther> =>
        throw new NotSupportedException();
    public static bool TryConvertFromSaturating<TOther>(TOther value, out BigRational result) where TOther : INumberBase<TOther> =>
        throw new NotSupportedException();
    public static bool TryConvertFromTruncating<TOther>(TOther value, out BigRational result) where TOther : INumberBase<TOther> =>
        throw new NotSupportedException();
    public static bool TryConvertToChecked<TOther>(BigRational value, out TOther result) where TOther : INumberBase<TOther> =>
        throw new NotSupportedException();
    public static bool TryConvertToSaturating<TOther>(BigRational value, out TOther result) where TOther : INumberBase<TOther> =>
        throw new NotSupportedException();
    public static bool TryConvertToTruncating<TOther>(BigRational value, out TOther result) where TOther : INumberBase<TOther> => 
        throw new NotSupportedException();
    public static bool TryParse(ReadOnlySpan<char> s, NumberStyles style, IFormatProvider? provider, out BigRational result) =>
        throw new NotSupportedException();
    public static bool TryParse(string? s, NumberStyles style, IFormatProvider? provider, out BigRational result) =>
        throw new NotSupportedException();
    
    public BigRational Add(BigRational rhs) => this + rhs;
    public BigRational Sub(BigRational rhs) => this - rhs;
    public BigRational Mul(BigRational rhs) => this * rhs;
    public BigRational Div(BigRational rhs) => this / rhs;
    public BigRational Min(BigRational rhs) => this < rhs ? this : rhs;
    public BigRational Max(BigRational rhs) => this > rhs ? this : rhs;

    public static BigRational Zero => new(0, 1);
    public static BigRational One => new(1, 1);

    public BigRational(BigInteger num) : this(num, 1) { }

    public static BigRational Create(BigInteger num, BigInteger denum) {
        if (denum.IsZero)
            throw new DivideByZeroException();
        if (denum.IsOne)
            return new BigRational(num, denum);
        BigInteger gcd = BigInteger.GreatestCommonDivisor(num, denum);
        return new BigRational(num / gcd, denum / gcd);
    }

    BigRational(BigInteger num, BigInteger denum) {
        Debug.Assert(!denum.IsZero);
        if (num.IsZero) {
            this.num = 0;
            this.denum = 1;
            return;
        }

        if (num.Sign < 0) {
            this.num = -num;
            this.denum = -denum;
        }
        else {
            this.num = num;
            this.denum = denum;
        }
        Debug.Assert(denum.IsOne || BigInteger.GreatestCommonDivisor(num, denum).IsOne);
    }

    // this is not a numeric comparison!!
    public int CompareTo(BigRational other) => 
        num.Equals(other.num) ? denum.CompareTo(other.denum) : num.CompareTo(other.num);

    public override bool Equals(object? obj) =>
        obj is BigRational other && Equals(other);

    public bool Equals(BigRational other) =>
        num.Equals(other.num) && denum.Equals(other.denum);

    public override int GetHashCode() =>
        HashCode.Combine(num, denum);

    public BigRational Abs() => num.Sign < 0 ? new BigRational(-num, denum) : this;

    public BigInteger GetInt() {
        Debug.Assert(IsInt);
        return num;
    }

    public static BigRational operator +(BigRational a, BigRational b) {
        if (a.IsZero)
            return b;
        if (b.IsZero)
            return a;
        return a.denum.Equals(b.denum) 
            ? Create(a.num + b.num, a.denum) 
            : Create(a.num * b.denum + b.num * a.denum, a.denum * b.denum);
    }

    public static BigRational operator -(BigRational a, BigRational b) {
        if (a.IsZero)
            return -b;
        if (b.IsZero)
            return a;
        return a.denum.Equals(b.denum)
            ? Create(a.num - b.num, a.denum)
            : Create(a.num * b.denum - b.num * a.denum, a.denum * b.denum);
    }

    public static BigRational operator -(BigRational a) =>
        a.IsZero ? a : new BigRational(-a.num, a.denum);

    public static BigRational operator *(BigRational a, BigRational b) {
        if (a.IsZero || b.IsZero)
            return Zero;
        return Create(a.num * b.num, a.denum * b.denum);
    }

    public static BigRational operator /(BigRational a, BigRational b) {
        if (b.IsZero)
            throw new DivideByZeroException();
        return a.IsZero ? Zero : Create(a.num * b.denum, a.denum * b.num);
    }

    public static bool operator ==(BigRational a, BigRational b) => a.Equals(b);
    public static bool operator !=(BigRational a, BigRational b) => !a.Equals(b);

    public static bool operator <(BigRational a, BigRational b) {
        if (a.denum.Equals(b.denum))
            return a.num < b.num;
        return a.num * b.denum < b.num * a.denum;
    }
    public static bool operator >=(BigRational a, BigRational b) => !(a < b);
    public static bool operator >(BigRational a, BigRational b) => b < a;
    public static bool operator <=(BigRational a, BigRational b) => b >= a;

    public bool LessThan(BigRational rhs) => this < rhs;
    public BigRational Negate() => -this;

    public override string ToString() =>
        denum.IsOne ? num.ToString() : $"{num} / {denum}";

    public string ToString(string? format, IFormatProvider? formatProvider) =>
        ToString();
}