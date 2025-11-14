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

    public override IEnumerable<NielsenEdge> Apply(LocalInfo info) {
        // V / Base^Power' Base' && Power' < Power
        // V / Base^Power V

        IntVar newPow = new();
        var power = new PowerToken(Power.Base, info.Env.IntPDDManager.MkPDD(newPow));
        var prefixes = StrManager.GetDecompose(info.CurrentNode, Power.Base, Forwards);
        Str s;
        foreach (var p in prefixes) {
            s = info.Env.StrManager.Concat(info.Env.MkString(power), p.Prefix, Forwards);
#if DEBUG
            var cmp = StrEqBase.LcpCompression(s, info.Env);
            if (cmp is not null)
                Console.WriteLine("Could have compressed: " + s + " => " + cmp);
#endif
            //s = StrEqBase.LcpCompression(s) ?? s;
            List<Constraint> cond = [
                IntLe.MkLe(info.Env.ZeroInt, info.Env.IntPDDManager.MkPDD(newPow)),
                IntLe.MkLt(info.Env.IntPDDManager.MkPDD(newPow), Power.Power),
            ];
            cond.AddRange(p.SideConstraints);
            if (p.VarDecomp is null) {
                info.CurrentNode.MkChild(info,
                    [new Subst(StrVarToken, s)], [],
                    cond, [], true);
                yield return info.CurrentNode.Outgoing[^1];
            }
            else {
                Debug.Assert(false);
                info.CurrentNode.MkChild(info,
                    [new Subst(StrVarToken, info.Env.StrManager.Subst(s, p.VarDecomp.Value)), p.VarDecomp.Value], [],
                    cond, [], false);
                yield return info.CurrentNode.Outgoing[^1];
            }
        }
        s = info.Env.MkString(new List<StrToken> {
            new PowerToken(Power.Base, Power.Power), StrVarToken,
        }, Forwards);
        info.CurrentNode.MkChild(info, [new Subst(StrVarToken, s)], [], [], [], false);
        yield return info.CurrentNode.Outgoing[^1];
    }

    protected override int CompareToInternal(ModifierBase otherM) {
        PowerSplitModifier other = (PowerSplitModifier)otherM;
        int cmp = Power.CompareTo(other.Power);
        if (cmp != 0)
            return cmp;
        cmp = StrVarToken.CompareTo(other.StrVarToken);
        return cmp != 0 ? cmp : -Forwards.CompareTo(other.Forwards);
    }

    public override string ToString() =>
        $"{StrVarToken} / ({Power.Base})^{{power}} [prefix({Power.Base})] && power < {Power.Power} \\/ {StrVarToken} / {(Forwards ? "" : StrVarToken + " ")}{Power}{(Forwards ? " " + StrVarToken : "")}";
}
