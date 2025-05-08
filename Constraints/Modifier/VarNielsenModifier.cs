using StringBreaker.Constraints.ConstraintElement;
using StringBreaker.IntUtils;
using StringBreaker.Tokens;

namespace StringBreaker.Constraints.Modifier;

public class VarNielsenModifier : DirectedNielsenModifier {

    public StrVarToken V1 { get; }
    public StrVarToken V2 { get; }

    public VarNielsenModifier(StrVarToken v1, StrVarToken v2, bool forward) : base(forward) {
        V1 = v1;
        V2 = v2;
    }

    public override void Apply(NielsenNode node) {
#if false
        // V1 / "" (progress)
        // V2 / "" && |V1| >= 1 (progress)
        // V1 / V2 && |V1| >= 1 && |V2| >= 1 (progress)
        // V1 / V1V2 && |V1| >= 1 && |V2| >= 1 (no progress)
        // V2 / V2V1 && |V1| >= 1 && |V2| >= 1 (no progress)
        var subst = new SubstVar(V1);
        var c = node.MkChild(node, [subst], true);
        c.Apply(subst);
        subst = new SubstVar(V2);
        c = node.MkChild(node, [subst], true);
        c.Apply(subst);
        var sc = IntLe.MkLe(new IntPoly(1), new IntPoly(new LenVar(V1)));
        c.AddConstraints(sc); // 1 <= |V1|
        c.Parent!.SideConstraints.Add(sc.Clone());

        Str s = [V2];
        subst = new SubstVar(V1, s);
        c = node.MkChild(node, [subst], true);
        c.Apply(subst);
        sc = IntLe.MkLe(new IntPoly(1), new IntPoly(new LenVar(V1)));
        c.AddConstraints(sc); // 1 <= |V1|
        c.Parent!.SideConstraints.Add(sc.Clone());
        sc = IntLe.MkLe(new IntPoly(1), new IntPoly(new LenVar(V2)));
        c.AddConstraints(sc); // 1 <= |V2|
        c.Parent!.SideConstraints.Add(sc.Clone());

        s = Forwards ? [V2, V1] : [V1, V2];
        subst = new SubstVar(V1, s);
        c = node.MkChild(node, [subst], false);
        c.Apply(subst);
        sc = IntLe.MkLe(new IntPoly(1), new IntPoly(new LenVar(V1)));
        c.AddConstraints(sc); // 1 <= |V1|
        c.Parent!.SideConstraints.Add(sc.Clone());
        sc = IntLe.MkLe(new IntPoly(1), new IntPoly(new LenVar(V2)));
        c.AddConstraints(sc); // 1 <= |V2|
        c.Parent!.SideConstraints.Add(sc.Clone());

        s = Forwards ? [V1, V2] : [V2, V1];
        subst = new SubstVar(V2, s);
        c = node.MkChild(node, [subst], false);
        c.Apply(subst);
        sc = IntLe.MkLe(new IntPoly(1), new IntPoly(new LenVar(V1)));
        c.AddConstraints(sc); // 1 <= |V1|
        c.Parent!.SideConstraints.Add(sc.Clone());
        sc = IntLe.MkLe(new IntPoly(1), new IntPoly(new LenVar(V2)));
        c.AddConstraints(sc); // 1 <= |V2|
        c.Parent!.SideConstraints.Add(sc.Clone());
#else
        // Legacy splitting
        // V1 / V2 (progress)
        // V1 / V1V2 (no progress)
        // V2 / V2V1 (no progress)
        Str s = [V2];
        node.MkChild(node, [new SubstVar(V1, s)], Array.Empty<Constraint>(), Array.Empty<DisEq>(), true);

        s = Forwards ? [V2, V1] : [V1, V2];
        node.MkChild(node,
            [new SubstVar(V1, s)],
            [IntLe.MkLt(new IntPoly(), new IntPoly(new LenVar(V1)))], // 0 < |V1|
            Array.Empty<DisEq>(), false);

        s = Forwards ? [V1, V2] : [V2, V1];
        node.MkChild(node,
            [new SubstVar(V2, s)],
            [IntLe.MkLt(new IntPoly(), new IntPoly(new LenVar(V2)))], // 0 < |V2|
            Array.Empty<DisEq>(), false);
#endif
    }

    protected override int CompareToInternal(ModifierBase otherM) {
        VarNielsenModifier other = (VarNielsenModifier)otherM;
        int cmp = Forwards.CompareTo(other.Forwards);
        if (cmp != 0)
            return cmp;
        cmp = V1.CompareTo(other.V1);
        return cmp != 0 ? cmp : V2.CompareTo(other.V2);
    }

    public override string ToString() =>
        //$"{V1} / ε || " +
        //$"{V2} / ε && |{V1}| > 0 || " +
        //$"{V1} / {V2}{V1} && |{V1}| > 0 && |{V2}| > 0 || " +
        //$"{V2} / {V2}{V1} && |{V1}| > 0 && |{V2}| > 0";
        $"{V1} / {V2} || " +
        $"{V1} / {V2}{V1} && |{V1}| > 0 || " +
        $"{V2} / {V1}{V2} && |{V2}| > 0 || ";
}