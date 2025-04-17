using System.Diagnostics;
using System.Numerics;

namespace StringBreaker.IntUtils;

public struct BigRational {

    readonly BigInteger num;
    readonly BigInteger denum;

    public bool IsZero => num.IsZero;
    public bool IsOne => num.IsOne && denum.IsOne;

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

    public override bool Equals(object? obj) =>
        obj is BigRational other && Equals(other);

    public bool Equals(BigRational other) =>
        num.Equals(other.num) && denum.Equals(other.denum);

    public override int GetHashCode() =>
        HashCode.Combine(num, denum);

    public BigRational Abs() => num.Sign < 0 ? new BigRational(-num, denum) : this;

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


    public override string ToString() =>
        denum.IsOne ? num.ToString() : $"{num} / {denum}";
}