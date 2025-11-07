using Microsoft.Z3;
using System.Diagnostics.Contracts;
using System.Numerics;
using ZIPT.IntUtils;
using ZIPT.Strings.Chunks;
using ZIPT.Strings.Tokens;

namespace ZIPT.Constraints;

public struct CharSubst {

    public SymCharToken Var { get; }
    public UnitToken Val { get; }
    public bool IsEliminating => Val is CharToken;

    public CharSubst(SymCharToken v, UnitToken s) {
        Var = v;
        Val = s;
    }

    public void AddToInterpretation(Interpretation itp) => itp.Apply(this);
    public void CollectValueSymbols(NonTermSet nonTermSet) => Val.CollectSymbols(nonTermSet, []);

    public override string ToString() => $"{Var} / {Val}";

    public override bool Equals(object? obj) =>
        obj is CharSubst substitution && Equals(substitution);

    public bool Equals(CharSubst subst) => Var.Equals(subst.Var) && Val.Equals(subst.Val);
    public override int GetHashCode() => HashCode.Combine(Var, Val);
}