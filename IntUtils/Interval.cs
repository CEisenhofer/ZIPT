using System.Diagnostics;
using System.Numerics;
using Microsoft.Z3;
using ZIPT.Constraints;

namespace ZIPT.IntUtils;

public readonly struct Interval {
    public readonly BigIntInf Min;
    public readonly BigIntInf Max;

    public static Interval Full => new(BigIntInf.NegInf, BigIntInf.PosInf);

    public bool IsFull => Min == BigIntInf.NegInf && Max == BigIntInf.PosInf;
    public bool IsUnit => Min == Max;

    public bool HasLow => Min != BigIntInf.NegInf;
    public bool HasHigh => Max != BigIntInf.PosInf;

    public Interval(BigIntInf minMax) {
        Min = minMax;
        Max = minMax;
    }

    public Interval(BigIntInf min, BigIntInf max) {
        Debug.Assert(min <= max);
        Min = min;
        Max = max;
    }

    public bool Contains(BigIntInf v) => 
        Min <= v && v <= Max;

    // Checks if Min <= i.Min && i.Max <= Max
    public bool Contains(Interval i) =>
        Min <= i.Min && i.Max <= Max;

    public static Interval operator +(Interval i, BigIntInf l) => new(i.Min + l, i.Max + l);
    public static Interval operator +(BigIntInf l, Interval i) => i + l;

    public static Interval operator +(Interval i1, Interval i2) {
        BigIntInf min, max;
        if (i1.Min.IsInf && i2.Min.IsInf && i1.Min.IsPos != i2.Min.IsPos)
            min = BigIntInf.NegInf;
        else
            min = i1.Min + i2.Min;
        if (i1.Max.IsInf && i2.Max.IsInf && i1.Max.IsPos != i2.Max.IsPos)
            max = BigIntInf.PosInf;
        else
            max = i1.Max + i2.Max;
        return new Interval(min, max);
    }

    public static Interval operator *(Interval i, BigIntInf fac) =>
        fac.IsPos
            ? new Interval(i.Min * fac, i.Max * fac)
            : new Interval(i.Max * fac, i.Min * fac);

    public static Interval operator *(BigIntInf fac, Interval i) => i * fac;

    // Round towards zero
    public static Interval operator /(Interval i, BigInteger d) {
        Debug.Assert(!d.IsZero);
        BigIntInf rl, rh;
        if (d.Sign < 0) {
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
        return new Interval(rl, rh);
    }

    public static bool operator ==(Interval i1, Interval i2) => i1.Equals(i2);
    public static bool operator !=(Interval i1, Interval i2) => !i1.Equals(i2);

    public Interval Negate() => new(-Max, -Min);

    public Interval MergeAddition(Interval other) => 
        new(Min + other.Min, Max + other.Max);

    public Interval MergeMultiplication(Interval other) {
        BigIntInf v1 = Min * other.Max;
        BigIntInf v2 = other.Min * Max;
        BigIntInf v3 = Max * other.Max;
        BigIntInf v4 = Min * other.Min;

        return new Interval(
            BigIntInf.Min(BigIntInf.Min(v1, v2), BigIntInf.Min(v3, v4)),
            BigIntInf.Max(BigIntInf.Max(v1, v2), BigIntInf.Max(v3, v4))
        );
    }

    public BoolExpr ToZ3Constraint(NonTermInt v, NielsenGraph graph) {
        if (IsFull)
            return graph.Ctx.MkTrue();
        IntExpr ve = v.ToExpr(graph);
        if (IsUnit) {
            Debug.Assert(!Min.IsInf);
            return graph.Ctx.MkEq(ve, ((BigInt)Min).ToExpr(graph));
        }
        if (Min.IsNegInf)
            return graph.Ctx.MkLe(ve, ((BigInt)Max).ToExpr(graph));
        if (Max.IsPosInf)
            return graph.Ctx.MkGe(ve, ((BigInt)Min).ToExpr(graph));
        return graph.Ctx.MkAnd(
            graph.Ctx.MkLe(ve, ((BigInt)Max).ToExpr(graph)),
            graph.Ctx.MkGe(ve, ((BigInt)Min).ToExpr(graph))
        );
    }

    public override bool Equals(object? obj) =>
        obj is Interval interval && Equals(interval);

    public bool Equals(Interval other) =>
        Min == other.Min && Max == other.Max;

    public override int GetHashCode() =>
        Min.GetHashCode() + 894440933 * Max.GetHashCode();

    public override string ToString() =>
        Min == Max ? Min.ToString() : $"[{Min}, {Max}]";
}