using ZIPT.Constraints.ConstraintElement;
using ZIPT.IntUtils;
using ZIPT.Strings.Chunks;
using ZIPT.Strings.Tokens;

namespace ZIPT.Constraints.Modifier;

// Variable-focused Nielsen splitting heuristics. Produces substitutions assigning one variable
// to another or to concatenations of variables, with optional length side-constraints.
public class VarNielsenModifier : DirectedNielsenModifier {

    public StrVarToken V1 { get; }
    public StrVarToken V2 { get; }

    public VarNielsenModifier(StrVarToken v1, StrVarToken v2, bool forward, DependencyTracker reason) : base(forward, reason) {
        V1 = v1;
        V2 = v2;
    }

    public override IEnumerable<NielsenEdge> Apply(LocalInfo info) {
#if false
        // V1 / "" (progress)
        // V2 / "" && |V1| >= 1 (progress)
        // V1 / V2 && |V1| >= 1 && |V2| >= 1 (progress)
        // V1 / V1V2 && |V1| >= 1 && |V2| >= 1 (no progress)
        // V2 / V2V1 && |V1| >= 1 && |V2| >= 1 (no progress)
        var subst = new Subst(V1);
        var c = node.MkChild(node, [subst], true);
        c.Apply(subst);
        subst = new Subst(V2);
        c = node.MkChild(node, [subst], true);
        c.Apply(subst);
        var sc = IntLe.MkLe(new PDD<BigInteger>(1), new PDD<BigInteger>(new LenVar(V1)));
        c.AddConstraints(sc); // 1 <= |V1|
        c.Parent!.SideConstraints.Add(sc.Clone());

        Str s = [V2];
        subst = new Subst(V1, s);
        c = node.MkChild(node, [subst], true);
        c.Apply(subst);
        sc = IntLe.MkLe(new PDD<BigInteger>(1), new PDD<BigInteger>(new LenVar(V1)));
        c.AddConstraints(sc); // 1 <= |V1|
        c.Parent!.SideConstraints.Add(sc.Clone());
        sc = IntLe.MkLe(new PDD<BigInteger>(1), new PDD<BigInteger>(new LenVar(V2)));
        c.AddConstraints(sc); // 1 <= |V2|
        c.Parent!.SideConstraints.Add(sc.Clone());

        s = Forwards ? [V2, V1] : [V1, V2];
        subst = new Subst(V1, s);
        c = node.MkChild(node, [subst], false);
        c.Apply(subst);
        sc = IntLe.MkLe(new PDD<BigInteger>(1), new PDD<BigInteger>(new LenVar(V1)));
        c.AddConstraints(sc); // 1 <= |V1|
        c.Parent!.SideConstraints.Add(sc.Clone());
        sc = IntLe.MkLe(new PDD<BigInteger>(1), new PDD<BigInteger>(new LenVar(V2)));
        c.AddConstraints(sc); // 1 <= |V2|
        c.Parent!.SideConstraints.Add(sc.Clone());

        s = Forwards ? [V1, V2] : [V2, V1];
        subst = new Subst(V2, s);
        c = node.MkChild(node, [subst], false);
        c.Apply(subst);
        sc = IntLe.MkLe(new PDD<BigInteger>(1), new PDD<BigInteger>(new LenVar(V1)));
        c.AddConstraints(sc); // 1 <= |V1|
        c.Parent!.SideConstraints.Add(sc.Clone());
        sc = IntLe.MkLe(new PDD<BigInteger>(1), new PDD<BigInteger>(new LenVar(V2)));
        c.AddConstraints(sc); // 1 <= |V2|
        c.Parent!.SideConstraints.Add(sc.Clone());
#else
        // Legacy variable splitting: produce variants assigning one variable to another or
        // concatenations of variables with optional length side constraints to prevent cycles.
        Str s = info.Env.MkString(V2);
        info.CurrentNode.MkChild(info, [new Subst(V1, s)], [], [], [], true);
        yield return info.CurrentNode.Outgoing[^1];

        s = Forwards ? info.Env.MkString(V2, V1) : info.Env.MkString(V1, V2);
        info.CurrentNode.MkChild(info,
            [new Subst(V1, s)], [],
            [IntLe.MkLt(info.Env.ZeroInt, LenVar.MkLenPoly(V1, info.Env), Reason)], [], // 0 < |V1|
            false);
        yield return info.CurrentNode.Outgoing[^1];

        s = Forwards ? info.Env.MkString(V1, V2) : info.Env.MkString(V2, V1);
        info.CurrentNode.MkChild(info,
            [new Subst(V2, s)], [],
            [IntLe.MkLt(info.Env.ZeroInt, LenVar.MkLenPoly(V2, info.Env), Reason)], [], // 0 < |V2|
            false);
        yield return info.CurrentNode.Outgoing[^1];
#endif
    }

    protected override int CompareToInternal(ModifierBase otherM) {
        VarNielsenModifier other = (VarNielsenModifier)otherM;
        int cmp = V1.CompareTo(other.V1);
        if (cmp != 0)
            return cmp;
        cmp = V2.CompareTo(other.V2);
        return cmp != 0 ? cmp : -Forwards.CompareTo(other.Forwards);
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