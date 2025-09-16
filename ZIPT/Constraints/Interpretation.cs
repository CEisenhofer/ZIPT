using System.Diagnostics;
using System.Numerics;
using ZIPT.MiscUtils;
using ZIPT.IntUtils;
using ZIPT.Strings.Chunks;
using ZIPT.Strings.Tokens;

namespace ZIPT.Constraints;

public class Interpretation {

    public Environment Env { get; }
    public Dictionary<IntVar, BigInteger> IntVal { get; } = [];
    public Dictionary<NamedStrToken, Str> Substitution { get; } = [];

    public PDD<BigInteger> ResolveVar(IntVar v) => IntVal.TryGetValue(v, out var i) 
        ? Env.IntPDDManager.MkPDD(i) 
        : Env.IntPDDManager.MkPDD(v);

    public Interpretation(Environment env) => 
        Env = env;

    public void Add(IntVar v, BigInteger l) {
        Debug.Assert(!IntVal.ContainsKey(v));
        IntVal[v] = l;
    }

    public void Apply(Subst subst) {
        List<(NamedStrToken k, Str v)> newDict = [];
        foreach (var kv in Substitution) {
            var n = Env.StrManager.Subst(kv.Value, subst);
            if (!ReferenceEquals(n, kv.Value))
                newDict.Add((kv.Key, n));
        }
        foreach (var (k, v) in newDict) {
            Substitution[k] = v;
        }
        if (!Substitution.ContainsKey(subst.Var))
            Substitution.Add(subst.Var, subst.Str);
    }

    public void Complete(HashSet<CharToken> alphabet) {
        NonTermSet nonTermSet = new();
        var ch = alphabet.IsNonEmpty() ? alphabet.First() : new CharToken('a');
        foreach (var v in Substitution.Values) {
            v.CollectSymbols(nonTermSet, []);
        }
        Interpretation clean = new(Env);
        foreach (var v in nonTermSet.IntVars) {
            clean.Add(v, !IntVal.ContainsKey(v) ? 0 : IntVal[v]);
        }
        foreach (var p in nonTermSet.StrVars.OfType<StrVarToken>()) {
            clean.Substitution.Add(p, Env.EmptyStr);
        }
        var prev = Substitution.ToList();
        Substitution.Clear();
        foreach (var p in prev) {
            Substitution.Add(p.Key, Env.StrManager.Subst(p.Value, clean));
        }
        foreach (var p in nonTermSet.StrVars) {
            Substitution.TryAdd(p, Env.EmptyStr);
        }
    }

    public void ProjectTo(NonTermSet nonTermSet) {

        List<NamedStrToken> toSRemove = [];
        List<IntVar> toIRemove = [];
        foreach (var v in Substitution.Keys) {
            if (!nonTermSet.Contains(v))
                toSRemove.Add(v);
        }
        foreach (var v in IntVal.Keys) {
            if (!nonTermSet.Contains(v))
                toIRemove.Add(v);
        }

        foreach (var v in toSRemove) {
            Substitution.Remove(v);
        }
        foreach (var i in toIRemove) {
            IntVal.Remove(i);
        }
    }

    public override string ToString() =>
        string.Join(";\n",
            Substitution
                .OrderBy(o => o.Key.Name)
                .Select(o => $"{o.Key} / {(o.Value.Length == 0 ? "ε" : o.Value)}")
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