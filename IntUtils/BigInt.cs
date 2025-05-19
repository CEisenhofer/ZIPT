using Microsoft.Z3;
using System.ComponentModel;
using System.Diagnostics;
using System.Numerics;
using ZIPT.Constraints;

namespace ZIPT.IntUtils;

public readonly struct BigInt : IArith<BigInt> {

    readonly BigInteger val;

    public bool IsZero => val.IsZero;
    public bool IsPos => val.Sign > 0;
    public bool IsNeg => val.Sign < 0;
    public bool IsOne => val.IsOne;
    public bool IsMinusOne => (-val).IsOne;

    public static BigInt Zero => new(BigInteger.Zero);
    public static BigInt One => new(BigInteger.One);

    public BigInt(BigInteger val) => this.val = val;
    public BigInt(BigInt val) => this.val = val.val;

    public static implicit operator BigInt(BigInteger val) => new(val);

    public static implicit operator BigInteger(BigInt val) => val.val;
    
    public static implicit operator BigInt(int val) => new((BigInteger)val);

    public static implicit operator BigInt(uint val) => new((BigInteger)val);

    public int CompareTo(BigInt other) => val.CompareTo(other.val);

    public BigInt Inc() => val + 1;
    public BigInt Add(BigInt rhs) => val + rhs.val;
    public static BigInt operator +(BigInt lhs, BigInt rhs) => lhs.Add(rhs);
    public BigInt Sub(BigInt rhs) => val - rhs.val;
    public static BigInt operator -(BigInt lhs, BigInt rhs) => lhs.Sub(rhs);
    public BigInt Mul(BigInt rhs) => val * rhs.val;
    public static BigInt operator *(BigInt lhs, BigInt rhs) => lhs.Mul(rhs);
    public BigInt Div(BigInt rhs) => val / rhs.val;
    public static BigInt operator /(BigInt lhs, BigInt rhs) => lhs.Div(rhs);
    public BigInt Rem(BigInt rhs) => val % rhs.val;
    public static BigInt operator %(BigInt lhs, BigInt rhs) => lhs.Rem(rhs);
    public BigInt Min(BigInt rhs) => BigInteger.Min(val, rhs.val);
    public BigInt Max(BigInt rhs) => BigInteger.Max(val, rhs.val);

    public (BigInt r, BigInt m) DivRem(BigInt d) {
        Debug.Assert(!d.IsZero);
        return IsZero
            ? (0, 0)
            : BigInteger.DivRem(val, d);
    }

    public static bool operator ==(BigInt left, BigInt right) => left.Equals(right);
    public static bool operator !=(BigInt left, BigInt right) => !left.Equals(right);
    public static bool operator <(BigInt left, BigInt right) => left.CompareTo(right) < 0;
    public static bool operator >(BigInt left, BigInt right) => left.CompareTo(right) > 0;
    public static bool operator <=(BigInt left, BigInt right) => left.CompareTo(right) <= 0;
    public static bool operator >=(BigInt left, BigInt right) => left.CompareTo(right) >= 0;
    
    public bool Equals(BigInt rhs) => val == rhs.val;
    public bool LessThan(BigInt rhs) => this < rhs;
    
    public BigInt Negate() => -val;
    public static BigInt operator -(BigInt val) => -val.val;
    public BigInt Abs() => BigInteger.Abs(val);

    public BigInteger GreatestCommonDivisor(BigInt t) {
        Debug.Assert(!IsZero);
        Debug.Assert(!t.IsZero);
        var gcd = BigInteger.GreatestCommonDivisor(val, t.val);
        Debug.Assert(gcd.Sign > 0);
        return gcd;
    }

    public bool TryGetInt(out int v) {
        v = 0;
        if (val < int.MinValue || val > int.MaxValue)
            return false;
        v = (int)val;
        return true;
    }

    public IntExpr ToExpr(NielsenGraph graph) => graph.Ctx.MkInt(val.ToString());

    public override bool Equals(object? obj) => obj is BigInt other && Equals(other);
    public override int GetHashCode() => val.GetHashCode();
    public override string ToString() => val.ToString();
}