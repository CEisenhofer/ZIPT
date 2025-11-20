using System.Diagnostics;
using System.Numerics;
using Microsoft.Z3;
using ZIPT.IntUtils;
using ZIPT.MiscUtils;
using ZIPT.Strings.Chunks;
using ZIPT.Strings.Tokens;
using ZIPT.Strings.Tokens.AuxTokens;
using static System.Net.WebRequestMethods;

namespace ZIPT.Constraints;

public class Interpretation {

    public Environment Env { get; }
    public Dictionary<IntVar, BigInteger> IntVal { get; } = [];
    public Dictionary<NamedStrToken, Subst> Substitution { get; } = [];
    public Dictionary<SymCharToken, CharSubst> CharSubstitution { get; } = [];

    public PDD<BigInteger> ResolveVar(IntVar v) => IntVal.TryGetValue(v, out var i) 
        ? Env.IntPDDManager.MkPDD(i) 
        : Env.IntPDDManager.MkPDD(v);

    public Interpretation(Environment env) => 
        Env = env;

    public void Add(IntVar v, BigInteger l) {
        Debug.Assert(!IntVal.ContainsKey(v));
        IntVal[v] = l;
    }

    public void Apply(Subst subst) => 
        Substitution[subst.Var] = new Subst(subst.Var, Env.StrManager.Subst(subst.Str, this));

    public void Apply(CharSubst subst) {
        Str s = Env.StrManager.Subst(Env.MkString(subst.Val), this);
        Debug.Assert(s is { Length: 1, First: UnitToken });
        UnitToken u = (UnitToken)s.First;
        CharSubstitution[subst.Var] = new CharSubst(subst.Var, u);
    }

    public void Complete(Model model, LocalInfo info) {
        NonTermSet nonTermSet = new();
        //var ch = alphabet.IsEmpty ? new CharToken('a') : alphabet.First;
        foreach (var v in Substitution.Values) {
            v.Str.CollectSymbols(nonTermSet, new CharacterSet());
        }
        Interpretation clean = new(Env);
        foreach (var v in nonTermSet.IntVars) {
            clean.Add(v, IntVal.GetValueOrDefault(v, BigInteger.Zero));
        }
        foreach (var p in nonTermSet.CharVars) {
            Expr c = model.Eval(Env.ValOf.Apply(p.ToExpr(Env, info.CurrentModificationCnt)), true);
            Debug.Assert(c is BitVecNum);
            clean.CharSubstitution.Add(p, new CharSubst(p, new CharToken((char)((BitVecNum)c).UInt)));
        }
        foreach (var p in nonTermSet.StrVars.OfType<StrVarToken>()) {
            clean.Substitution.Add(p, new Subst(p, Env.EmptyStr));
        }
        var prev = Substitution.ToList();
        Substitution.Clear();
        foreach (var p in prev) {
            Substitution.Add(p.Key, new Subst(p.Key, Env.StrManager.Subst(p.Value.Str, clean)));
        }
        foreach (var p in nonTermSet.StrVars) {
            Substitution.TryAdd(p, new Subst(p, Env.EmptyStr));
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

    public void Simplify() {
        List<NamedStrToken> keys = Substitution.Keys.ToList();
        foreach (var k in keys) {
            Substitution[k] = new Subst(k, Env.StrManager.Simplify(Substitution[k].Str));
        }
    }

    public override string ToString() =>
        string.Join(";\n",
            Substitution
                .OrderBy(o => o.Key.Name)
                .Select(o => o.Value.ToString())
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