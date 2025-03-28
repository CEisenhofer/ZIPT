using System.Diagnostics;
using Microsoft.Z3;
using StringBreaker.Constraints;
using StringBreaker.Tokens;

namespace StringBreaker.IntUtils;

public class IntVar : NonTermInt {
    
    static int nextId;
    public int Id { get; }
    public override Len MinLen => Len.NegInf;

    public IntVar(int id) => 
        Id = id;

    public IntVar() : this(nextId++) { }

    public override bool Equals(object? obj) => obj is IntVar var && Equals(var);
    public bool Equals(IntVar other) => Id == other.Id;

    public override int GetHashCode() => Id.GetHashCode() * 919174721;

    public override Poly Apply(Subst subst) => new(new StrictMonomial(this));
    public override Poly Apply(Interpretation subst) => subst.ResolveVar(this);

    public override int CompareToInternal(NonTermInt other) => 
        Id.CompareTo(((IntVar)other).Id);

    public override void CollectSymbols(HashSet<NamedStrToken> vars, HashSet<SymCharToken> sChars, HashSet<IntVar> iVars,
        HashSet<CharToken> alphabet) => iVars.Add(this);

    public override IntExpr ToExpr(NielsenGraph graph) {
        if (graph.Cache.GetCachedIntExpr(this) is { } e)
            return e;
        e = graph.Ctx.MkIntConst(ToString());
        graph.Cache.SetCachedExpr(this, e);
        return e;
    }

    public override string ToString() => $"#n{Id}";
}