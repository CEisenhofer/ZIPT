using System.Diagnostics;
using ZIPT.MiscUtils;
using ZIPT.Constraints.ConstraintElement;
using ZIPT.IntUtils;
using ZIPT.Tokens;

namespace ZIPT.Constraints.Modifier;

public class PowerSplitModifier : DirectedNielsenModifier {
    public StrVarToken Var { get; }
    public PowerToken Power { get; }

    public PowerSplitModifier(StrVarToken var, PowerToken power, bool forward) : base(forward) {
        Var = var;
        Power = power;
    }

    public override void Apply(NielsenNode node) {
        // V / Base^Power' Base' && Power' < Power
        // V / Base^Power V

        IntVar newPow = new();
        var power = new PowerToken(Power.Base.Clone(), new IntPoly(newPow));
        var prefixes = Power.Base.GetPrefixes(Forwards);
        Str s;
        foreach (var p in prefixes) {
            s = new Str(power);
            s.AddRange(p.str, Forwards);
#if DEBUG
            var cmp = StrEqBase.LcpCompression(s);
            if (cmp is not null)
                Console.WriteLine("Could have compressed: " + s + " => " + cmp);
#endif
            //s = StrEqBase.LcpCompression(s) ?? s;
            List<Constraint> cond = [
                IntLe.MkLe(new IntPoly(0), new IntPoly(newPow)),
                IntLe.MkLt(new IntPoly(newPow), Power.Power),
            ];
            cond.AddRange(p.sideConstraints);
            if (p.varDecomp is null)
                node.MkChild(node, 
                    [new SubstVar(Var, s)],
                    cond, Array.Empty<DisEq>(), true);
            else {
                Debug.Assert(false);
                node.MkChild(node,
                    [new SubstVar(Var, s.Apply(p.varDecomp)), p.varDecomp],
                    cond, Array.Empty<DisEq>(), false);
            }
        }
        s = new Str(Var);
        s.Add(new PowerToken(Power.Base.Clone(), Power.Power.Clone()), Forwards);
        node.MkChild(node, [new SubstVar(Var, s)], Array.Empty<Constraint>(), Array.Empty<DisEq>(), false);
    }

    protected override int CompareToInternal(ModifierBase otherM) {
        PowerSplitModifier other = (PowerSplitModifier)otherM;
        int cmp = Power.CompareTo(other.Power);
        if (cmp != 0)
            return cmp;
        cmp = Var.CompareTo(other.Var);
        return cmp != 0 ? cmp : Forwards.CompareTo(other.Forwards);
    }

    public override string ToString() =>
        $"{Var} / ({Power.Base})^{{power}} [prefix({Power.Base})] && power < {Power.Power} \\/ {Var} / {(Forwards ? "" : Var + " ")}{Power}{(Forwards ? " " + Var : "")}";
}
