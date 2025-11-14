using System.Diagnostics;
using System.Numerics;
using System.Runtime.CompilerServices;
using Microsoft.Z3;
using ZIPT.Constraints;

namespace ZIPT.IntUtils;

public readonly struct Interval<T> where T : INumberBase<T>, IComparable<T> {
    public readonly InfNum<T> Min;
    public readonly InfNum<T> Max;

    public static Interval<T> Full => new(InfNum<T>.NegInfNum, InfNum<T>.PosInfNum);

    public bool IsFull => Min == InfNum<T>.NegInfNum && Max == InfNum<T>.PosInfNum;
    public bool IsUnit => Min == Max;

    public bool HasLow => Min != InfNum<T>.NegInfNum;
    public bool HasHigh => Max != InfNum<T>.PosInfNum;

    public Interval(InfNum<T> minMax) {
        Min = minMax;
        Max = minMax;
    }

    public Interval(InfNum<T> min, InfNum<T> max) {
        Debug.Assert(min <= max);
        Min = min;
        Max = max;
    }

    public bool Contains(T v) => 
        Min <= v && v <= Max;

    public bool Contains(InfNum<T> v) => 
        Min <= v && v <= Max;

    // Checks if Min <= i.Min && i.Max <= Max
    public bool Contains(Interval<T> i) =>
        Min <= i.Min && i.Max <= Max;

    public static Interval<T> operator +(Interval<T> i, InfNum<T> l) => new(i.Min + l, i.Max + l);
    public static Interval<T> operator +(InfNum<T> l, Interval<T> i) => i + l;

    public static Interval<T> operator +(Interval<T> i1, Interval<T> i2) {
        InfNum<T> min, max;
        if (i1.Min.IsInf && i2.Min.IsInf && i1.Min.IsPos != i2.Min.IsPos)
            min = InfNum<T>.NegInfNum;
        else
            min = i1.Min + i2.Min;
        if (i1.Max.IsInf && i2.Max.IsInf && i1.Max.IsPos != i2.Max.IsPos)
            max = InfNum<T>.PosInfNum;
        else
            max = i1.Max + i2.Max;
        return new Interval<T>(min, max);
    }

    public static Interval<T> operator *(Interval<T> i, InfNum<T> fac) =>
        fac.IsPos
            ? new Interval<T>(i.Min * fac, i.Max * fac)
            : new Interval<T>(i.Max * fac, i.Min * fac);

    public static Interval<T> operator *(InfNum<T> fac, Interval<T> i) => i * fac;

    // Round towards zero
    public static Interval<T> operator /(Interval<T> i, T d) {
        Debug.Assert(!T.IsZero(d));
        InfNum<T> rl, rh;
        if (T.IsNegative(d)) {
            rh = i.Min.Div(d);
            rl = i.Max.Div(d);
        }
        else {
            rh = i.Max.Div(d);
            rl = i.Min.Div(d);
        }

        // BigInteger ml, mh;
        //if (d.Sign < 0) {
        //    (rh, mh) = i.Min.DivRem(d);
        //    (rl, ml) = i.Max.DivRem(d);
        //}
        //else {
        //   (rl, ml) = i.Min.DivRem(d);
        //   (rh, mh) = i.Max.DivRem(d);
        //}
        //if (!ml.IsZero)
        //    rl--;
        //if (!mh.IsZero)
        //    rh++;
        return new Interval<T>(rl, rh);
    }

    public static bool operator ==(Interval<T> i1, Interval<T> i2) => i1.Equals(i2);
    public static bool operator !=(Interval<T> i1, Interval<T> i2) => !i1.Equals(i2);

    public Interval<T> Negate() => new(-Max, -Min);

    public Interval<T> MergeAddition(Interval<T> other) => 
        new(Min + other.Min, Max + other.Max);

    public Interval<T> MergeMultiplication(Interval<T> other) {
        if (Min.IsNegInf && other.Max.IsPosInf ||
            other.Min.IsNegInf && Max.IsPosInf)
            return Full;
        var v1 = Min * other.Max;
        var v2 = other.Min * Max;
        var v3 = Max * other.Max;
        var v4 = Min * other.Min;

        return new Interval<T>(
            InfNum<T>.Min(InfNum<T>.Min(v1, v2), InfNum<T>.Min(v3, v4)),
            InfNum<T>.Max(InfNum<T>.Max(v1, v2), InfNum<T>.Max(v3, v4))
        );
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static IntExpr ToExpr(BigInteger i, Environment env) {
        if (i >= long.MinValue && i <= long.MaxValue)
            return env.Ctx.MkInt((long)i);
        return env.Ctx.MkInt(i.ToString());
    }

    public static BoolExpr ToZ3Constraint(Interval<BigInteger> interval, NamedInt v, LocalInfo info) {
        if (interval.IsFull)
            return info.Ctx.MkTrue();
        IntExpr ve = v.ToExpr(info.Env, info.CurrentModificationCnt);
        if (interval.IsUnit) {
            Debug.Assert(!interval.Min.IsInf);
            return info.Ctx.MkEq(ve, ToExpr((BigInteger)interval.Min, info.Env));
        }
        if (interval.Min.IsNegInf)
            return info.Ctx.MkLe(ve, ToExpr((BigInteger)interval.Max, info.Env));
        if (interval.Max.IsPosInf)
            return info.Ctx.MkGe(ve, ToExpr((BigInteger)interval.Min, info.Env));
        return info.Ctx.MkAnd(
            info.Ctx.MkLe(ve, ToExpr((BigInteger)interval.Max, info.Env)),
            info.Ctx.MkGe(ve, ToExpr((BigInteger)interval.Min, info.Env))
        );
    }

    public override bool Equals(object? obj) =>
        obj is Interval<T> interval && Equals(interval);

    public bool Equals(Interval<T> other) =>
        Min == other.Min && Max == other.Max;

    public override int GetHashCode() =>
        Min.GetHashCode() + 894440933 * Max.GetHashCode();

    public override string ToString() =>
        Min == Max ? Min.ToString() : $"[{Min}, {Max}]";
}