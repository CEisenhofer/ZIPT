using System.Diagnostics;
using System.Text;
using ZIPT.IntUtils;
using ZIPT.Strings.Tokens;

namespace ZIPT.Constraints;

public class NonTermSet {

    // Maybe sorted list instead of hashset? ...
    public HashSet<NamedStrToken> StrVars { get; } = [];
    public HashSet<SymCharToken> CharVars { get; } = [];
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
    public void Add(SymCharToken charVar) => CharVars.Add(charVar);
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
    public void Remove(SymCharToken charVar) => CharVars.Remove(charVar);
    public void Remove(IntVar intVar) => IntVars.Remove(intVar);

    public bool Contains(NamedStrToken strVar) => StrVars.Contains(strVar);
    public bool Contains(SymCharToken charVar) => CharVars.Contains(charVar);
    public bool Contains(IntVar intVar) => IntVars.Contains(intVar);

    public NonTermSet Clone() {
        NonTermSet clone = new();
        foreach (var strVar in StrVars) {
            clone.StrVars.Add(strVar);
        }
        foreach (var charVar in CharVars) {
            clone.CharVars.Add(charVar);
        }
        foreach (var intVar in IntVars) {
            clone.IntVars.Add(intVar);
        }
        return clone;
    }

    public override string ToString() {
        StringBuilder sb = new();
        sb.Append("String Variables: ");
        foreach (var strVar in StrVars) {
            sb.Append('\t').AppendLine(strVar.ToString());
        }
        sb.AppendLine();
        sb.Append("Char Variables: ");
        foreach (var charVar in CharVars) {
            sb.Append('\t').AppendLine(charVar.ToString());
        }
        sb.AppendLine();
        sb.Append("Integer Variables: ");
        foreach (var intVar in IntVars) {
            sb.Append('\t').AppendLine(intVar.ToString());
        }
        return sb.ToString();
    }
}