using System.Diagnostics;
using System.Text;
using ZIPT.IntUtils;
using ZIPT.Tokens;

namespace ZIPT.Constraints;

public class NonTermSet {

    // Maybe sorted list instead of hashset? ...
    public HashSet<NamedStrToken> StrVars { get; } = [];
    public HashSet<IntVar> IntVars { get; } = [];
    public HashSet<SymCharToken> SymChars { get; } = [];

    public int Count => StrVars.Count + IntVars.Count + SymChars.Count;

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
    public void Add(SymCharToken symChar) => SymChars.Add(symChar);

    public void Add(NonTermSet set) {
        foreach (var c in set.StrVars) {
            StrVars.Add(c);
        }
        foreach (var c in set.IntVars) {
            IntVars.Add(c);
        }
        foreach (var c in set.SymChars) {
            SymChars.Add(c);
        }
    }

    public void Remove(NamedStrToken strVar) => StrVars.Remove(strVar);
    public void Remove(IntVar intVar) => IntVars.Remove(intVar);
    public void Remove(SymCharToken symChar) => SymChars.Remove(symChar);

    public bool Contains(NamedStrToken strVar) => StrVars.Contains(strVar);
    public bool Contains(IntVar intVar) => IntVars.Contains(intVar);
    public bool Contains(SymCharToken symChar) => SymChars.Contains(symChar);

    public NonTermSet Clone() {
        NonTermSet clone = new();
        foreach (var strVar in StrVars) {
            clone.StrVars.Add(strVar);
        }
        foreach (var intVar in IntVars) {
            clone.IntVars.Add(intVar);
        }
        foreach (var symChar in SymChars) {
            clone.SymChars.Add(symChar);
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

        var (c1, c2) =
            set1.SymChars.Count < set2.SymChars.Count
                ? (set1.SymChars, set2.SymChars)
                : (set2.SymChars, set1.SymChars);
        Debug.Assert(c1.Count <= c2.Count);
        foreach (var symChar in c1) {
            if (c2.Contains(symChar))
                return true;
        }
        return false;
    }

    public void Add(Subst subst) {
        switch (subst) {
            case SubstVar sv:
                Add(sv.Var);
                break;
            case SubstSChar sc:
                Add(sc.Sym);
                break;
            default:
                Debug.Assert(false);
                break;
        }
    }

    public void Apply(Subst subst) {
        subst.CollectValueSymbols(this);
    }

    public void Apply(Interpretation itp) {
        foreach (var s in itp.Substitution.Values) {
            s.CollectSymbols(this, []);
        }
        foreach (var s in itp.CharSubstitution.Values) {
            if (s is SymCharToken sc) {
                Add(sc);
            }
            else {
                Debug.Assert(s is CharToken);
            }
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
        sb.AppendLine();
        sb.Append("Symbolic Characters: ");
        foreach (var symChar in SymChars) {
            sb.Append('\t').AppendLine(symChar.ToString());
        }
        return sb.ToString();
    }
}