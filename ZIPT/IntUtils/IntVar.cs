using System.Diagnostics;
using System.Numerics;
using Microsoft.Z3;
using ZIPT.Constraints;
using ZIPT.Strings;
using ZIPT.Strings.Tokens;

namespace ZIPT.IntUtils;

public class IntVar : NamedInt {
    
    static uint nextId;
    public uint IntVarId { get; }
    public override InfNum<BigInteger> MinLen => InfNum<BigInteger>.NegInfNum;

    public IntVar(uint intVarId) => 
        IntVarId = intVarId;

    public IntVar() : this(nextId++) { }

    public override bool Equals(object? obj) => obj is IntVar var && Equals(var);
    public bool Equals(IntVar other) => IntVarId == other.IntVarId;

    public override int GetHashCode() => IntVarId.GetHashCode() * 919174721;

    public override int CompareToInternal(NamedInt other) => 
        IntVarId.CompareTo(((IntVar)other).IntVarId);

    public override void CollectSymbols(NonTermSet nonTermSet, HashSet<CharToken> alphabet) => nonTermSet.Add(this);

    public override IntExpr ToExpr(NielsenGraph graph) {
        if (graph.Env.GetCachedIntExpr(this, graph) is { } e)
            return e;
        e = graph.Ctx.MkIntConst(ToString());
        graph.Env.SetCachedExpr(this, e, graph);
        return e;
    }

    public override string ToString() => $"#n{IntVarId}";
}