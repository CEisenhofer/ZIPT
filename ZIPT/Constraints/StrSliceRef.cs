namespace ZIPT.Constraints;

public class StrSliceRef : IEquatable<StrSliceRef> {

    readonly StrSlice reference;
    
    public StrSliceRef(StrSlice reference) => 
        this.reference = reference;

    public override bool Equals(object? obj) =>
            obj is StrSliceRef other && Equals(other);
    public bool Equals(StrSliceRef? other) =>
        other is not null && reference.Equals(other.reference);
    public override int GetHashCode() => reference.GetHashCode();
    public override string ToString() => reference.ToString();
}