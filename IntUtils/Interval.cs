using System.Diagnostics;

namespace StringBreaker.IntUtils;

public struct Interval {
    public readonly Len Min;
    public readonly Len Max;

    public static Interval Full => new(Len.NegInf, Len.PosInf);

    public bool IsFull => Min == Len.NegInf && Max == Len.PosInf;
    public bool IsUnit => Min == Max;

    public Interval(Len minMax) {
        Min = minMax;
        Max = minMax;
    }

    public Interval(Len min, Len max) {
        Debug.Assert(min <= max);
        Min = min;
        Max = max;
    }

    public bool Contains(Len v) => 
        Min <= v && v <= Max;

    public static Interval operator +(Interval i, Len l) => new(i.Min + l, i.Max + l);
    public static Interval operator +(Len l, Interval i) => i + l;

    public static Interval operator +(Interval i1, Interval i2) {
        Len min, max;
        if (i1.Min.IsInf && i2.Min.IsInf && i1.Min.IsPos != i2.Min.IsPos)
            min = Len.NegInf;
        else
            min = i1.Min + i2.Min;
        if (i1.Max.IsInf && i2.Max.IsInf && i1.Max.IsPos != i2.Max.IsPos)
            max = Len.PosInf;
        else
            max = i1.Max + i2.Max;
        return new Interval(min, max);
    }

    public static Interval operator *(Interval i, Len fac) =>
        fac.IsPos
            ? new Interval(i.Min * fac, i.Max * fac)
            : new Interval(i.Max * fac, i.Min * fac);

    public static Interval operator *(Len fac, Interval i) => i * fac;

    public static bool operator ==(Interval i1, Interval i2) => i1.Equals(i2);
    public static bool operator !=(Interval i1, Interval i2) => !i1.Equals(i2);

    public Interval MergeAddition(Interval other) => 
        new(Min + other.Min, Max + other.Max);

    public Interval MergeMultiplication(Interval other) {
        Len min1 = Min * other.Max;
        Len min2 = other.Min * Max;

        Len max1 = Max * other.Max;
        Len max2 = Min * other.Min;

        Len min = min1 < min2 ? min1 : min2;
        Len max = max1 > max2 ? max1 : max2;
        return new Interval(min, max);
    }

    public static bool Intersect(Interval i1, Interval i2) =>
        i1.Min >= i2.Min && i1.Min <= i2.Max ||
        i1.Max >= i2.Min && i1.Max <= i2.Max;

    public override bool Equals(object? obj) =>
        obj is Interval interval && Equals(interval);

    public bool Equals(Interval other) =>
        Min == other.Min && Max == other.Max;

    public override int GetHashCode() =>
        Min.GetHashCode() + 894440933 * Max.GetHashCode();

    public override string ToString() =>
        Min == Max ? Min.ToString() : $"[{Min}, {Max}]";
}