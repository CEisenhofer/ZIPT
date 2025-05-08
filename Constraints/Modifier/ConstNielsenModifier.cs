using StringBreaker.Constraints.ConstraintElement;
using StringBreaker.Tokens;

namespace StringBreaker.Constraints.Modifier;

public class ConstNielsenModifier : DirectedNielsenModifier {

    public StrVarToken V { get; }
    public StrToken T { get; }

    public ConstNielsenModifier(StrVarToken v, StrToken t, bool forward) : base(forward) {
        V = v;
        T = t;
    }

    public override void Apply(NielsenNode node) {
        // V / "" (progress)
        // V / T V (no progress)
        var subst = new SubstVar(V);
        node.MkChild(node, [subst], Array.Empty<Constraint>(), Array.Empty<DisEq>(), true);
        subst = new SubstVar(V, Forwards ? [T, V] : [V, T]);
        node.MkChild(node, [subst], Array.Empty<Constraint>(), Array.Empty<DisEq>(), false);
    }

    protected override int CompareToInternal(ModifierBase otherM) {
        ConstNielsenModifier other = (ConstNielsenModifier)otherM;
        int cmp = Forwards.CompareTo(other.Forwards);
        if (cmp != 0)
            return cmp;
        cmp = V.CompareTo(other.V);
        return cmp != 0 ? cmp : T.CompareTo(other.T);
    }

    public override string ToString() => 
        $"{V} / ε || {V} / {(Forwards ? (V.ToString() + T) : (T + V.ToString()))}";
}