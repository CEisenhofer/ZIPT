using System.Diagnostics;
using ZIPT.MiscUtils;
using ZIPT.IntUtils;
using ZIPT.Tokens;

namespace ZIPT.Constraints;

public class Interpretation {

    public Dictionary<IntVar, BigInt> IntVal { get; } = [];
    public Dictionary<NamedStrToken, Str> Substitution { get; } = [];
    public Dictionary<SymCharToken, UnitToken> CharSubstitution { get; } = [];

    public Str ResolveVar(NamedStrToken v) => Substitution.TryGetValue(v, out var s) ? s : [v];
    public UnitToken ResolveVar(SymCharToken v) => CharSubstitution.GetValueOrDefault(v, v);
    public IntPoly ResolveVar(IntVar v) => IntVal.TryGetValue(v, out var i) ? new IntPoly(i) : new IntPoly(v);

    public void Add(SubstVar subst) => 
        Substitution[subst.Var] = subst.Str.Apply(this);

    public void Add(SubstSChar subst) => 
        CharSubstitution[subst.Sym] = subst.C is SymCharToken c ? ResolveVar(c) : subst.C;

    public void Add(IntVar v, BigInt l) {
        Debug.Assert(!IntVal.ContainsKey(v));
        IntVal[v] = l;
    }

    public void Complete(HashSet<CharToken> alphabet) {
        NonTermSet nonTermSet = new();
        var ch = alphabet.IsNonEmpty() ? alphabet.First() : new CharToken('a');
        foreach (var v in Substitution.Values) {
            v.CollectSymbols(nonTermSet, []);
        }
        Interpretation clean = new();
        foreach (var v in nonTermSet.StrVars) {
            clean.Add(new SubstVar(v));
        }
        foreach (var c in nonTermSet.SymChars) {
            clean.Add(new SubstSChar(c, ch));
        }
        foreach (var v in nonTermSet.IntVars) {
            clean.Add(v, !IntVal.ContainsKey(v) ? 0 : IntVal[v]);
        }
        var prev = Substitution.ToList();
        Substitution.Clear();
        foreach (var p in prev) {
            Substitution.Add(p.Key, p.Value.Apply(clean));
        }
        foreach (var p in nonTermSet.StrVars) {
            Substitution.TryAdd(p, []);
        }
        var prev2 = CharSubstitution.ToList();
        CharSubstitution.Clear();
        foreach (var p in prev2) {
            CharSubstitution.Add(p.Key, p.Value is SymCharToken c ? clean.ResolveVar(c) : p.Value);
        }
        foreach (var p in nonTermSet.SymChars) {
            CharSubstitution.TryAdd(p, ch);
        }
    }

    public void ProjectTo(NonTermSet nonTermSet) {

        List<NamedStrToken> toSRemove = [];
        List<SymCharToken> toCRemove = [];
        List<IntVar> toIRemove = [];
        foreach (var v in Substitution.Keys) {
            if (!nonTermSet.Contains(v))
                toSRemove.Add(v);
        }
        foreach (var v in CharSubstitution.Keys) {
            if (!nonTermSet.Contains(v))
                toCRemove.Add(v);
        }
        foreach (var v in IntVal.Keys) {
            if (!nonTermSet.Contains(v))
                toIRemove.Add(v);
        }

        foreach (var v in toSRemove) {
            Substitution.Remove(v);
        }
        foreach (var c in toCRemove) {
            CharSubstitution.Remove(c);
        }
        foreach (var i in toIRemove) {
            IntVal.Remove(i);
        }
    }

    public override string ToString() =>
        string.Join(";\n",
            Substitution
                .OrderBy(o => o.Key.Name)
                .Select(o => $"{o.Key} / {o.Value}")
                .Concat(
                    IntVal.Select(o => $"{o.Key} := {o.Value}")));

    public override bool Equals(object? obj) =>
        obj is Interpretation itp && Equals(itp);

    public bool Equals(Interpretation itp) =>
        Substitution.Count == itp.Substitution.Count &&
        IntVal.Count == itp.IntVal.Count &&
        Substitution.All(kv => itp.Substitution.TryGetValue(kv.Key, out var v) && kv.Value.Equals(v)) &&
        IntVal.All(kv => itp.IntVal.TryGetValue(kv.Key, out var v) && kv.Value.Equals(v));

    public override int GetHashCode() =>
        HashCode.Combine(
            Substitution.Aggregate(739474559, (o, v) => 519455297 * o + v.GetHashCode()),
            IntVal.Aggregate(153281669, (o, v) => 211955069 * o + v.GetHashCode())
        );
}