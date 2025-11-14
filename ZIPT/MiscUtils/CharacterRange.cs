using System.Diagnostics;

namespace ZIPT.MiscUtils;

// [From, To)
public readonly struct CharacterRange : IEquatable<CharacterRange>, IComparable<CharacterRange> {
    public readonly uint From;
    public readonly uint To; // excluding!

    public bool IsEmpty => From == To;
    public bool IsFull => From == CharacterSet.MinChar && To == CharacterSet.MaxChar + 1;
    public bool IsUnit => Length == 1;
    public uint Length => To - From;

    public CharacterRange(uint c) : this(c, c + 1) { }

    public CharacterRange(uint from, uint to) {
        From = from;
        To = to;
        Debug.Assert(from <= to);
    }

    public bool Contains(uint c) =>
        c >= From && c <= To;

    public int Find(uint c) =>
        c < From ? -1 : c >= To ? 1 : 0;

    public override bool Equals(object? obj) =>
        obj is CharacterRange other && Equals(other);

    public bool Equals(CharacterRange other) =>
        From == other.From && To == other.To;

    public override int GetHashCode() =>
        HashCode.Combine(From, To);

    public static string GetChar(uint c) =>
        c is
            >= 'a' and <= 'z' or
            >= 'A' and <= 'Z' or
            >= '0' and <= '9'
            ? ((char)c).ToString()
            : $"#[{c}]";

    public int CompareTo(CharacterRange other) {
        int cmp = From.CompareTo(other.From);
        return cmp != 0 ? cmp : To.CompareTo(other.To);
    }

    public override string ToString() {
        if (IsEmpty)
            return "[]";
        if (IsFull)
            return "[..]";
        if (From + 1 == To)
            return GetChar(From);
        if (From + 2 == To)
            return $"[{GetChar(From)}{GetChar(To - 1)}]";
        return $"[{GetChar(From)}-{GetChar(To - 1)}]";
    }
}