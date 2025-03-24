namespace StringBreaker.IntUtils;

public class RefInt {
    
    public RefInt(int val) => 
        Val = val;

    public int Val { get; set; }

    public int Inc() => Val++;

    public override bool Equals(object? obj) =>
        obj is RefInt i && Val == i.Val;

    public static bool operator ==(RefInt i1, RefInt i2) => i1.Val == i2.Val;
    public static bool operator !=(RefInt i1, RefInt i2) => i1.Val != i2.Val;

    public override int GetHashCode() => Val.GetHashCode();

    public override string ToString() => Val.ToString();
}