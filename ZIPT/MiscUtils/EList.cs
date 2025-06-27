namespace ZIPT.MiscUtils;

public class EList<T> : List<T>, IEquatable<EList<T>> where T : notnull {

    public EList() { }
    public EList(IEnumerable<T> collection) : base(collection) { }

    public override bool Equals(object? obj) => 
        obj is EList<T> other && Equals(other);

    public bool Equals(EList<T>? other) =>
        other is not null && Count == other.Count && this.SequenceEqual(other);

    public override int GetHashCode() => 
        this.Aggregate(847664327, (current, item) => current * 258134111 + item.GetHashCode());
}