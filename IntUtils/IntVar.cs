using Microsoft.Z3;
using StringBreaker.Constraints;
using StringBreaker.Tokens;

namespace StringBreaker.IntUtils;

public class IntVar : NonTermInt {
    
    public static int NextId;
    public int Id { get; }

    public IntVar(int id) => 
        Id = id;

    public IntVar() : this(NextId++) { }

    public override bool Equals(object? obj) => obj is IntVar var && Equals(var);
    public bool Equals(IntVar other) => Id == other.Id;

    public override int GetHashCode() => Id.GetHashCode() * 919174721;
    public override Poly Apply(Subst subst) => new(new StrictMonomial(this));
    public override Poly Apply(Interpretation subst) => subst.ResolveVar(this);

    public override int CompareTo(NonTermInt? other) {
        if (other is IntVar var)
            return Id.CompareTo(var.Id);
        return 1;
    }

    public override void CollectSymbols(HashSet<StrVarToken> vars, HashSet<CharToken> alphabet) { }

    public override IntExpr ToExpr(NielsenGraph graph) {
        if (graph.Propagator.GetCachedIntExpr(this) is { } e)
            return e;
        e = graph.Ctx.MkIntConst(ToString());
        graph.Propagator.SetCachedExpr(this, e);
        return e;
    }

    public override string ToString() => $"#n{Id}";
}