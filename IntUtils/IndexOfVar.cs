using Microsoft.Z3;
using StringBreaker.Constraints;
using StringBreaker.Strings;

namespace StringBreaker.IntUtils;

public class IndexOfVar : IntVar {

    public Str S { get; }
    public Str Contained { get; }
    public Poly Start { get; }

    public override Len MinLen => -1;

    public IndexOfVar(Str s, Str contained, Poly start) {
        S = s;
        Contained = contained;
        Start = start;
    }

    public override IntExpr ToExpr(NielsenContext ctx) => 
        (IntExpr)ctx.Cache.IndexOfFct.Apply(S.ToExpr(), Contained.ToExpr(), Start.ToExpr());

    public sealed override string ToString() => $"indexOf({S},{Contained},{Start})";
}