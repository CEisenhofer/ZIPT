using System.Diagnostics;

namespace ZIPT.MiscUtils;

readonly struct TriangleMatrix : IEquatable<TriangleMatrix> {

    readonly uint l1, l2, l3;

    // 1 l1 l2
    // 0 1  l3
    // 0 0  1
    public TriangleMatrix(object o) {
        Debug.Assert(o is not null);
        uint hash = (uint)o.GetHashCode() * 615382997;

        l1 = hash & 0xFFFF;
        hash >>= 16;
        l2 = hash & 0xFF;
        hash >>= 8;
        l3 = hash;
    }

    public TriangleMatrix(in TriangleMatrix m1, in TriangleMatrix m2) {
        long l1L = (long)m1.l1 + m2.l1;
        long l2L = m1.l2 + (long)m1.l1 * m2.l3 + m2.l2;
        long l3L = m1.l3 + m2.l3;
        // int.MaxValue [2^32 - 1] is a prime number
        l1 = (uint)(l1L % int.MaxValue);
        l2 = (uint)(l2L % int.MaxValue);
        l3 = (uint)(l3L % int.MaxValue);
    }

    public override bool Equals(object? obj) =>
        obj is TriangleMatrix other && Equals(other);

    public bool Equals(TriangleMatrix other) =>
        l1 == other.l1 && l2 == other.l2 && l3 == other.l3;

    public override int GetHashCode() =>
        HashCode.Combine(l1, l2, l3);
}