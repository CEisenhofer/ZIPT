using System.Diagnostics;
using StringBreaker.Strings;
using StringBreaker.Strings.Tokens;

namespace StringBreaker.Constraints.Modifier;

public class VarPaddingModifier : DirectedNielsenModifier {

    public StrVarToken Var { get; }
    public int Padding { get; }

    public VarPaddingModifier(StrVarToken var, int padding, bool forward) : base(forward) {
        Var = var;
        Padding = padding;
        Debug.Assert(padding > 0);
    }

    public override void Apply(NielsenContext ctx) {
        // For all 0 <= i < Padding: V / o_1 ... o_i (progress)
        // V / o_1 ... o_{Padding} V (no progress)
        Str s;
        SymCharToken[] ch = new SymCharToken[Padding];
        NielsenNode? c;
        SubstVar subst;
        for (int i = 0; i < Padding; i++) {
            ch[i] = new SymCharToken();
            s = [];
            for (int j = 0; j < i; j++) {
                s.Add(ch[j]);
            }
            subst = new SubstVar(Var, s);
            c = ctx.CurrentNode.MkChild(ctx, [subst], true);
            c.Apply(subst);
        }

        s = [];
        for (int j = 0; j < Padding; j++) {
            s.Add(ch[j]);
        }
        s.Add(Var, !Forwards);

        subst = new SubstVar(Var, s);
        c = ctx.CurrentNode.MkChild(ctx, [subst], false);
        c.Apply(subst);
    }

    protected override int CompareToInternal(ModifierBase otherM) {
        VarPaddingModifier other = (VarPaddingModifier)otherM;
        int cmp = Padding.CompareTo(other.Padding);
        if (cmp != 0)
            return cmp;
        cmp = Var.CompareTo(other.Var);
        return cmp != 0 ? cmp : Forwards.CompareTo(other.Forwards);
    }

    public override string ToString() => 
        $"\\// {Var} / {(Forwards ? "" : Var + " ")}[0..{Padding - 1} times sym. char] || {Var} / {(Forwards ? "" : Var + " ")}[{Padding} times sym. char]{(Forwards ? " " + Var : "")}";
}