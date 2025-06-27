namespace ZIPT.IntUtils;

public interface IArith<T> : IComparable<T> {

    public bool IsZero { get; }
    public bool IsPos { get; }
    public bool IsNeg { get; }
    public bool IsOne { get; }
    public bool IsMinusOne { get; }

    public T Inc();
    public T Add(T rhs);
    public T Sub(T rhs);
    public T Mul(T rhs);
    public T Div(T rhs);

    public T Min(T rhs);
    public T Max(T rhs);

    public bool Equals(T rhs);
    public bool LessThan(T rhs);

    public T Negate();
    public T Abs();
}