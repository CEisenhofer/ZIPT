using StringBreaker.Constraints.ConstraintElement;
using StringBreaker.IntUtils;
using StringBreaker.Tokens;

namespace StringBreaker.Constraints.Modifier;

public class VarNielsenModifier : DirectedNielsenModifier {

    public StrVarToken Var1 { get; }
    public StrVarToken Var2 { get; }

    public VarNielsenModifier(StrVarToken v1, StrVarToken v2, bool forward) : base(forward) {
        Var1 = v1;
        Var2 = v2;
    }

    public override void Apply(NielsenNode node) {
        // V1 = ""
        // V2 = "" && |V1| >= 1
        // V1 = V2 && |V1| >= 1 && |V2| >= 1
        // V1 = V1V2 && |V1| >= 1 && |V2| >= 1
        // V2 = V2V1 && |V1| >= 1 && |V2| >= 1
        var subst = new SubstVar(Var1);
        var c = node.MkChild(node, [subst]);
        c.Apply(subst);
        subst = new SubstVar(Var2);
        c = node.MkChild(node, [subst]);
        c.Apply(subst);
        var sc = IntLe.MkLe(new Poly(1), new Poly(new LenVar(Var1)));
        c.AddConstraints(sc); // 1 <= |V1|
        c.Parent!.SideConstraints.Add(sc.Clone());

        Str s = [Var2];
        subst = new SubstVar(Var1, s);
        c = node.MkChild(node, [subst]);
        c.Apply(subst);
        sc = IntLe.MkLe(new Poly(1), new Poly(new LenVar(Var1)));
        c.AddConstraints(sc); // 1 <= |V1|
        c.Parent!.SideConstraints.Add(sc.Clone());
        sc = IntLe.MkLe(new Poly(1), new Poly(new LenVar(Var2)));
        c.AddConstraints(sc); // 1 <= |V2|
        c.Parent!.SideConstraints.Add(sc.Clone());

        s = Forwards ? [Var2, Var1] : [Var1, Var2];
        subst = new SubstVar(Var1, s);
        c = node.MkChild(node, [subst]);
        c.Apply(subst);
        sc = IntLe.MkLe(new Poly(1), new Poly(new LenVar(Var1)));
        c.AddConstraints(sc); // 1 <= |V1|
        c.Parent!.SideConstraints.Add(sc.Clone());
        sc = IntLe.MkLe(new Poly(1), new Poly(new LenVar(Var2)));
        c.AddConstraints(sc); // 1 <= |V2|
        c.Parent!.SideConstraints.Add(sc.Clone());

        s = Forwards ? [Var1, Var2] : [Var2, Var1];
        subst = new SubstVar(Var2, s);
        c = node.MkChild(node, [subst]);
        c.Apply(subst);
        sc = IntLe.MkLe(new Poly(1), new Poly(new LenVar(Var1)));
        c.AddConstraints(sc); // 1 <= |V1|
        c.Parent!.SideConstraints.Add(sc.Clone());
        sc = IntLe.MkLe(new Poly(1), new Poly(new LenVar(Var2)));
        c.AddConstraints(sc); // 1 <= |V2|
        c.Parent!.SideConstraints.Add(sc.Clone());
    }

    protected override int CompareToInternal(ModifierBase otherM) {
        VarNielsenModifier other = (VarNielsenModifier)otherM;
        int cmp = Forwards.CompareTo(other.Forwards);
        if (cmp != 0)
            return cmp;
        cmp = Var1.CompareTo(other.Var1);
        return cmp != 0 ? cmp : Var2.CompareTo(other.Var2);
    }

    public override string ToString() => 
        $"{Var1} / ε || " +
        $"{Var2} / ε && |{Var1}| > 0 || " +
        $"{Var1} / {Var2}{Var1} && |{Var1}| > 0 && |{Var2}| > 0 || " +
        $"{Var2} / {Var2}{Var1} && |{Var1}| > 0 && |{Var2}| > 0";
}