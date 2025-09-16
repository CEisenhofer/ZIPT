using System.Diagnostics;
using System.Numerics;
using System.Xml.Linq;
using ZIPT.Constraints.ConstraintElement;
using ZIPT.IntUtils;
using ZIPT.MiscUtils;
using ZIPT.Strings;
using ZIPT.Strings.Chunks;
using ZIPT.Strings.Tokens;

namespace ZIPT.Constraints.Modifier;

public class PowerSplitModifier : DirectedNielsenModifier {
    public StrVarToken StrVarToken { get; }
    public PowerToken Power { get; }

    public PowerSplitModifier(StrVarToken strVar, PowerToken power, bool forward) : base(forward) {
        StrVarToken = strVar;
        Power = power;
    }

    public override void Apply(NielsenNode node) {
        // V / Base^Power' Base' && Power' < Power
        // V / Base^Power V

        IntVar newPow = new();
        var power = new PowerToken(Power.Base, node.Env.IntPDDManager.MkPDD(newPow));
        var prefixes = StrManager.GetPrefixes(node, Power.Base, Forwards);
        Str s;
        foreach (var p in prefixes) {
            if (Forwards)
                s = node.Env.StrManager.Concat(node.Env.MkString(power), p.Str);
            else
                s = node.Env.StrManager.Concat(p.Str, node.Env.MkString(power));
#if DEBUG
            var cmp = StrEqBase.LcpCompression(s, node.Env);
            if (cmp is not null)
                Console.WriteLine("Could have compressed: " + s + " => " + cmp);
#endif
            //s = StrEqBase.LcpCompression(s) ?? s;
            List<Constraint> cond = [
                IntLe.MkLe(node.Env.ZeroInt, node.Env.IntPDDManager.MkPDD(newPow)),
                IntLe.MkLt(node.Env.IntPDDManager.MkPDD(newPow), Power.Power),
            ];
            cond.AddRange(p.SideConstraints);
            if (p.VarDecomp is null)
                node.MkChild(node, 
                    [new Subst(StrVarToken, s)],
                    cond, true);
            else {
                Debug.Assert(false);
                node.MkChild(node,
                    [new Subst(StrVarToken, node.Env.StrManager.Subst(s, p.VarDecomp.Value)), p.VarDecomp.Value],
                    cond, false);
            }
        }
        if (Forwards)
            s = node.Env.MkString(StrVarToken, new PowerToken(Power.Base, Power.Power));
        else
            s = node.Env.MkString(new PowerToken(Power.Base, Power.Power), StrVarToken);
        node.MkChild(node, [new Subst(StrVarToken, s)], Array.Empty<Constraint>(), false);
    }

    protected override int CompareToInternal(ModifierBase otherM) {
        PowerSplitModifier other = (PowerSplitModifier)otherM;
        int cmp = Power.CompareTo(other.Power);
        if (cmp != 0)
            return cmp;
        cmp = StrVarToken.CompareTo(other.StrVarToken);
        return cmp != 0 ? cmp : Forwards.CompareTo(other.Forwards);
    }

    public override string ToString() =>
        $"{StrVarToken} / ({Power.Base})^{{power}} [prefix({Power.Base})] && power < {Power.Power} \\/ {StrVarToken} / {(Forwards ? "" : StrVarToken + " ")}{Power}{(Forwards ? " " + StrVarToken : "")}";
}
