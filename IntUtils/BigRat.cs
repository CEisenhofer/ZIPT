using System.Diagnostics;
using System.Numerics;

namespace ZIPT.IntUtils;

public struct BigRat : IArith<BigRat> {

    readonly BigInteger num;
    readonly BigInteger denum;

    public bool IsZero => num.IsZero;
    public bool IsPos => num.Sign > 0;
    public bool IsNeg => num.Sign < 0;
    public bool IsOne => num.IsOne && denum.IsOne;
    public bool IsMinusOne => (-this).IsOne;
    public bool IsInt => denum.IsOne;

    public BigRat Inc() => this + One;
    public BigRat Add(BigRat rhs) => this + rhs;
    public BigRat Sub(BigRat rhs) => this - rhs;
    public BigRat Mul(BigRat rhs) => this * rhs;
    public BigRat Div(BigRat rhs) => this / rhs;
    public BigRat Min(BigRat rhs) => this < rhs ? this : rhs;
    public BigRat Max(BigRat rhs) => this > rhs ? this : rhs;

    public static BigRat Zero => new(0, 1);
    public static BigRat One => new(1, 1);

    public BigRat(BigInteger num) : this(num, 1) { }
    public BigRat(BigInt num) : this(num, 1) { }

    public static BigRat Create(BigInteger num, BigInteger denum) {
        if (denum.IsZero)
            throw new DivideByZeroException();
        if (denum.IsOne)
            return new BigRat(num, denum);
        BigInteger gcd = BigInteger.GreatestCommonDivisor(num, denum);
        return new BigRat(num / gcd, denum / gcd);
    }

    BigRat(BigInteger num, BigInteger denum) {
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
    public int CompareTo(BigRat other) => 
        num.Equals(other.num) ? denum.CompareTo(other.denum) : num.CompareTo(other.num);

    public override bool Equals(object? obj) =>
        obj is BigRat other && Equals(other);

    public bool Equals(BigRat other) =>
        num.Equals(other.num) && denum.Equals(other.denum);

    public override int GetHashCode() =>
        HashCode.Combine(num, denum);

    public BigRat Abs() => num.Sign < 0 ? new BigRat(-num, denum) : this;

    public BigInteger GetInt() {
        Debug.Assert(IsInt);
        return num;
    }

    public static BigRat operator +(BigRat a, BigRat b) {
        if (a.IsZero)
            return b;
        if (b.IsZero)
            return a;
        return a.denum.Equals(b.denum) 
            ? Create(a.num + b.num, a.denum) 
            : Create(a.num * b.denum + b.num * a.denum, a.denum * b.denum);
    }

    public static BigRat operator -(BigRat a, BigRat b) {
        if (a.IsZero)
            return -b;
        if (b.IsZero)
            return a;
        return a.denum.Equals(b.denum)
            ? Create(a.num - b.num, a.denum)
            : Create(a.num * b.denum - b.num * a.denum, a.denum * b.denum);
    }

    public static BigRat operator -(BigRat a) =>
        a.IsZero ? a : new BigRat(-a.num, a.denum);

    public static BigRat operator *(BigRat a, BigRat b) {
        if (a.IsZero || b.IsZero)
            return Zero;
        return Create(a.num * b.num, a.denum * b.denum);
    }

    public static BigRat operator /(BigRat a, BigRat b) {
        if (b.IsZero)
            throw new DivideByZeroException();
        return a.IsZero ? Zero : Create(a.num * b.denum, a.denum * b.num);
    }

    public static bool operator ==(BigRat a, BigRat b) => a.Equals(b);
    public static bool operator !=(BigRat a, BigRat b) => !a.Equals(b);

    public static bool operator <(BigRat a, BigRat b) {
        if (a.denum.Equals(b.denum))
            return a.num < b.num;
        return a.num * b.denum < b.num * a.denum;
    }
    public static bool operator >=(BigRat a, BigRat b) => !(a < b);
    public static bool operator >(BigRat a, BigRat b) => b < a;
    public static bool operator <=(BigRat a, BigRat b) => b >= a;

    public bool LessThan(BigRat rhs) => this < rhs;
    public BigRat Negate() => -this;

    public override string ToString() =>
        denum.IsOne ? num.ToString() : $"{num} / {denum}";
}