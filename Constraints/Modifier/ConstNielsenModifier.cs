using StringBreaker.Tokens;

namespace StringBreaker.Constraints.Modifier;

public class ConstNielsenModifier : DirectedNielsenModifier {

    public StrVarToken V { get; }
    public StrToken Prefix { get; }

    public ConstNielsenModifier(StrVarToken v, StrToken pr, bool forward) : base(forward) {
        V = v;
        Prefix = pr;
    }

    public override void Apply(NielsenNode node) {
        // V / "" (progress)
        // V / Prefix V (no progress)
        var subst = new SubstVar(V);
        var c = node.MkChild(node, [subst], true);
        c.Apply(subst);
        subst = new SubstVar(V, Forwards ? [Prefix, V] : [V, Prefix]);
        c = node.MkChild(node, [subst], false);
        c.Apply(subst);
    }

    protected override int CompareToInternal(ModifierBase otherM) {
        ConstNielsenModifier other = (ConstNielsenModifier)otherM;
        int cmp = Forwards.CompareTo(other.Forwards);
        if (cmp != 0)
            return cmp;
        cmp = V.CompareTo(other.V);
        return cmp != 0 ? cmp : Prefix.CompareTo(other.Prefix);
    }

    public override string ToString() => 
        $"{V} / ε || {V} / {(Forwards ? (V.ToString() + Prefix) : (Prefix + V.ToString()))}";
}