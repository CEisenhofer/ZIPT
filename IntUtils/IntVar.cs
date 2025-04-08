using System.Diagnostics;
using Microsoft.Z3;
using StringBreaker.Constraints;
using StringBreaker.Strings;
using StringBreaker.Strings.Tokens;

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

    public override IntExpr ToExpr(NielsenContext ctx) {
        if (ctx.Cache.GetCachedIntExpr(this, ctx) is { } e)
            return e;
        e = ctx.Ctx.MkIntConst(ToString());
        ctx.Cache.SetCachedExpr(this, e, ctx);
        return e;
    }

    public override string ToString() => $"#n{Id}";
}