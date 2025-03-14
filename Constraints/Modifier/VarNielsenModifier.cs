using StringBreaker.Constraints.ConstraintElement;
using StringBreaker.IntUtils;
using StringBreaker.Tokens;

namespace StringBreaker.Constraints.Modifier;

public class VarNielsenModifier : DirectedNielsenModifier {

    public StrVarToken Var1 { get; }
    public StrVarToken Var2 { get; }

    public VarNielsenModifier(StrVarToken v1, StrVarToken v2, bool backward) : base(backward) {
        Var1 = v1;
        Var2 = v2;
    }

    public override void Apply(NielsenNode node) {
        // V1 = ""
        // V2 = "" && |V1| > 0
        // V1 = V1V2 && |V1| > 0
        // V2 = V2V1 && |V1| > 0 && |V2| > 0
        var subst = new Subst(Var1);
        var c = node.MkChild(node, [subst]);
        foreach (var cnstr in c.AllStrConstraints) {
            cnstr.Apply(subst);
        }
        subst = new Subst(Var2);
        c = node.MkChild(node, [subst]);
        foreach (var cnstr in c.AllStrConstraints) {
            cnstr.Apply(subst);
        }
        var sc = new Poly();
        sc.AddPoly(new Poly(1));
        sc.AddPoly(new Poly(new LenVar(Var1)));
        c.AddConstraints(new IntLe(sc)); // 1 - |V1| <= 0
        c.Parent!.SideConstraints.Add(new IntLe(sc.Clone()));

        Str s = Backwards ? [Var1, Var2] : [Var2, Var1];
        subst = new Subst(Var1, s);
        c = node.MkChild(node, [subst]);
        foreach (var cnstr in c.AllStrConstraints) {
            cnstr.Apply(subst);
        }
        sc = new Poly();
        sc.AddPoly(new Poly(1));
        sc.AddPoly(new Poly(new LenVar(Var1)));
        c.AddConstraints(new IntLe(sc)); // 1 - |V1| <= 0
        c.Parent!.SideConstraints.Add(new IntLe(sc.Clone()));

        s = Backwards ? [Var2, Var1] : [Var1, Var2];
        subst = new Subst(Var2, s);
        c = node.MkChild(node, [subst]);
        foreach (var cnstr in c.AllStrConstraints) {
            cnstr.Apply(subst);
        }
        sc = new Poly();
        sc.AddPoly(new Poly(1));
        sc.AddPoly(new Poly(new LenVar(Var1)));
        c.AddConstraints(new IntLe(sc)); // 1 - |V1| <= 0
        c.Parent!.SideConstraints.Add(new IntLe(sc.Clone()));
        sc = new Poly();
        sc.AddPoly(new Poly(1));
        sc.AddPoly(new Poly(new LenVar(Var2)));
        c.AddConstraints(new IntLe(sc)); // 1 - |V2| <= 0
        c.Parent!.SideConstraints.Add(new IntLe(sc.Clone()));
    }

    protected override int CompareToInternal(ModifierBase otherM) {
        VarNielsenModifier other = (VarNielsenModifier)otherM;
        int cmp = Backwards.CompareTo(other.Backwards);
        if (cmp != 0)
            return cmp;
        cmp = Var1.CompareTo(other.Var1);
        return cmp != 0 ? cmp : Var2.CompareTo(other.Var2);
    }

    public override string ToString() => 
        $"{Var1} / ε || " +
        $"{Var2} / ε && |{Var1}| > 0 || " +
        $"{Var1} / {Var2}{Var1} && |{Var1}| > 0 || " +
        $"{Var2} / {Var2}{Var1} && |{Var1}| > 0 && |{Var2}| > 0";
}