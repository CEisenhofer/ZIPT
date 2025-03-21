using Microsoft.Z3;
using StringBreaker.Tokens;

namespace StringBreaker;

public class ParikhInfo : IDisposable {

    public CharToken Char { get; }
    public FuncDecl Total { get; }
    // 1st argument: string; 2nd argument: modulo
    public Dictionary<uint, FuncDecl> Residual { get; }

    public ParikhInfo(CharToken c, OuterStringPropagator propagator) {
        Char = c;
        Context ctx = propagator.Ctx;
        Total = ctx.MkUserPropagatorFuncDecl("#" + c.Value, [propagator.StringSort], ctx.IntSort);
        propagator.InvParikInfo.Add(Total, new InvParikhInfo(this));
        Residual = [];
    }

    public void Dispose() {
        Total.Dispose();
        foreach (var decl in Residual.Values) {
            decl.Dispose();
        }
    }

    public FuncDecl GetResidual(uint mod, OuterStringPropagator propagator) {
        if (Residual.TryGetValue(mod, out var decl))
            return decl;

        Context ctx = propagator.Ctx;
        Residual.Add(mod,
            decl = ctx.MkUserPropagatorFuncDecl(
                "#" + Char.Value + "%" + mod, [propagator.StringSort, ctx.IntSort], ctx.IntSort));

        propagator.InvParikInfo.Add(decl, new InvParikhInfo(this, mod));
        return decl;
    }

    public override string ToString() => 
        $"Info for {Char}";
}

public class InvParikhInfo {

    public ParikhInfo Info { get; }
    uint Pos { get; }

    public bool IsTotal => Pos == 0;

    public uint ResidualMod => Pos == 0 ? 0 : Pos - 1;

    public InvParikhInfo(ParikhInfo info) {
        Info = info;
        Pos = 0;
    }

    public InvParikhInfo(ParikhInfo info, uint mod) {
        Info = info;
        Pos = mod + 1;
    }

    public override string ToString() =>
        $"InvInfo for {Info.Char} {(IsTotal ? "Sum" : "Mod " + ResidualMod)}";
}