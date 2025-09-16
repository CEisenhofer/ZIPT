using System.Diagnostics;
using System.Text;
using ZIPT.IntUtils;
using ZIPT.Strings.Tokens;

namespace ZIPT.Constraints;

public class NonTermSet {

    // Maybe sorted list instead of hashset? ...
    public HashSet<NamedStrToken> StrVars { get; } = [];
    public HashSet<IntVar> IntVars { get; } = [];

    public int Count => StrVars.Count + IntVars.Count;

    public NonTermSet() { }

    public NonTermSet(params NamedStrToken[] strVars) {
        foreach (var strVar in strVars) {
            StrVars.Add(strVar);
        }
    }

    public NonTermSet(params IntVar[] intVars) {
        foreach (var intVar in intVars) {
            IntVars.Add(intVar);
        }
    }

    public void Add(NamedStrToken strVar) => StrVars.Add(strVar);
    public void Add(IntVar intVar) => IntVars.Add(intVar);

    public void Add(NonTermSet set) {
        foreach (var c in set.StrVars) {
            StrVars.Add(c);
        }
        foreach (var c in set.IntVars) {
            IntVars.Add(c);
        }
    }

    public void Remove(NamedStrToken strVar) => StrVars.Remove(strVar);
    public void Remove(IntVar intVar) => IntVars.Remove(intVar);

    public bool Contains(NamedStrToken strVar) => StrVars.Contains(strVar);
    public bool Contains(IntVar intVar) => IntVars.Contains(intVar);

    public NonTermSet Clone() {
        NonTermSet clone = new();
        foreach (var strVar in StrVars) {
            clone.StrVars.Add(strVar);
        }
        foreach (var intVar in IntVars) {
            clone.IntVars.Add(intVar);
        }
        return clone;
    }

    public static bool IsIntersecting(NonTermSet set1, NonTermSet set2) {
        var (s1, s2) = 
            set1.StrVars.Count < set2.StrVars.Count 
            ? (set1.StrVars, set2.StrVars) 
            : (set2.StrVars, set1.StrVars);
        Debug.Assert(s1.Count <= s2.Count);
        foreach (var strVar in s1) {
            if (s2.Contains(strVar))
                return true;
        }

        var (i1, i2) = 
            set1.IntVars.Count < set2.IntVars.Count 
                ? (set1.IntVars, set2.IntVars) 
                : (set2.IntVars, set1.IntVars);
        Debug.Assert(i1.Count <= i2.Count);
        foreach (var intVar in i1) {
            if (i2.Contains(intVar))
                return true;
        }
        return false;
    }

    public void Add(Subst subst) {
        Add(subst.Var);
    }

    public void Apply(Subst subst) {
        subst.CollectValueSymbols(this);
    }

    public void Apply(Interpretation itp) {
        foreach (var s in itp.Substitution.Values) {
            s.CollectSymbols(this, []);
        }
    }



    public override string ToString() {
        StringBuilder sb = new();
        sb.Append("String Variables: ");
        foreach (var strVar in StrVars) {
            sb.Append('\t').AppendLine(strVar.ToString());
        }
        sb.AppendLine();
        sb.Append("Integer Variables: ");
        foreach (var intVar in IntVars) {
            sb.Append('\t').AppendLine(intVar.ToString());
        }
        return sb.ToString();
    }
}