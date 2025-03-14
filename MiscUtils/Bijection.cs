using System.Diagnostics;
using System.Diagnostics.CodeAnalysis;
using System.Text;

namespace StringBreaker.MiscUtils;

public class Bijection<T1, T2> where T1 : class where T2 : class {

    Dictionary<T1, T2> Forward { get; } = [];
    Dictionary<T2, T1> Backward { get; } = [];

    public int Count
    {
        get
        {
            Debug.Assert(Forward.Count == Backward.Count);
            return Forward.Count;
        }
    }

    public void Add(T1 t1, T2 t2) {
        bool s1 = Forward.TryAdd(t1, t2);
        bool s2 = Backward.TryAdd(t2, t1);
        Debug.Assert(s1 && s2);
    }

    public void Remove1(T1 t1) {
        T2 t2 = Forward[t1];
        bool s1 = Forward.Remove(t1);
        bool s2 = Backward.Remove(t2);
        Debug.Assert(s1 && s2);
    }

    public void Remove2(T2 t2) {
        T1 t1 = Backward[t2];
        bool s1 = Forward.Remove(t1);
        bool s2 = Backward.Remove(t2);
        Debug.Assert(s1 && s2);
    }

    public T1 GetT1(T2 t2) => Backward[t2];
    public T2 GetT2(T1 t1) => Forward[t1];

    public bool Contains1(T1 t1) => Forward.ContainsKey(t1);
    public bool Contains2(T2 t2) => Backward.ContainsKey(t2);

    public bool TryGetT1(T2 t2, [NotNullWhen(true)] out T1? t1) => Backward.TryGetValue(t2, out t1);
    public bool TryGetT2(T1 t1, [NotNullWhen(true)] out T2? t2) => Forward.TryGetValue(t1, out t2);

    public void Clear() {
        Forward.Clear();
        Backward.Clear();
    }

    public override string ToString() {
        Debug.Assert(Forward.Count == Backward.Count);

        StringBuilder sb = new();
        foreach (var (t1, t2) in Forward) {
            Debug.Assert(Backward[t2] == t1);
            sb.AppendLine($"{t1} <-> {t2}");
        }
        return sb.ToString();
    }
}