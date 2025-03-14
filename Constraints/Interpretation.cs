using System.Diagnostics;
using StringBreaker.IntUtils;
using StringBreaker.Tokens;

namespace StringBreaker.Constraints;

public class Interpretation {

    public Dictionary<IntVar, Len> IntVal { get; } = [];
    public Dictionary<StrVarToken, Str> Substitution { get; } = [];

    public Str ResolveVar(StrVarToken v) => Substitution.TryGetValue(v, out var s) ? s : [v];
    public Poly ResolveVar(IntVar v) => IntVal.TryGetValue(v, out var i) ? new Poly(i) : new Poly(v);

    public void AddBackwards(Subst subst) {
        Str res = subst.Str;
        foreach (var s in Substitution) {
            res = res.Apply(new Subst(s.Key, s.Value));
        }
        Substitution[subst.Var] = res;
    }

    public void AddIntVal(IntVar v, Len l) {
        Debug.Assert(!IntVal.ContainsKey(v));
        IntVal[v] = l;
    }

    public void Complete() {
        HashSet<StrVarToken> vars = [];
        foreach (var v in Substitution.Values) {
            v.CollectSymbols(vars, []);
        }
        Interpretation clean = new();
        foreach (var v in vars) {
            clean.AddBackwards(new Subst(v));
        }
        var prev = Substitution.ToList();
        Substitution.Clear();
        foreach (var p in prev) {
            Substitution.Add(p.Key, p.Value.Apply(clean));
        }
        foreach (var p in vars) {
            Substitution.TryAdd(p, []);
        }
    }

    public override string ToString() =>
        string.Join(";\n",
            Substitution
                .Select(o => $"{o.Key} / {o.Value}")
                .Concat(
                    IntVal.Select(o => $"{o.Key} := {o.Value}")));

    public override bool Equals(object? obj) =>
        obj is Interpretation interpretation && Equals(interpretation);

    public bool Equals(Interpretation interpretation) =>
        Substitution.Count == interpretation.Substitution.Count &&
        Substitution.All(kv => interpretation.Substitution.TryGetValue(kv.Key, out var v) && kv.Value.Equals(v));

    public override int GetHashCode() => 
        Substitution.Aggregate(739474559, (o, v) => 519455297 * o + v.GetHashCode());
}