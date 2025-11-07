using ZIPT.Constraints.ConstraintElement;
using ZIPT.Strings;
using ZIPT.Strings.Tokens;

namespace ZIPT.Constraints.Modifier;

public class ConstNielsenModifier : DirectedNielsenModifier {

    public StrVarToken V { get; }
    public StrToken T { get; }

    public ConstNielsenModifier(StrVarToken v, StrToken t, bool forward) : base(forward) {
        V = v;
        T = t;
    }

    public override IEnumerable<NielsenEdge> Apply(NielsenNode node) {
        // V / "" (progress)
        // V / T V (no progress)
        var subst = new Subst(V, node.Env.EmptyStr);
        node.MkChild(node, [subst], Array.Empty<Constraint>(), [], true);
        yield return node.Outgoing[^1];
        
        subst = new Subst(V, Forwards
            ? node.Env.MkString(T, V)
            : node.Env.MkString(V, T)
        );
        node.MkChild(node, [subst], Array.Empty<Constraint>(), [], false);
        yield return node.Outgoing[^1];
    }

    protected override int CompareToInternal(ModifierBase otherM) {
        ConstNielsenModifier other = (ConstNielsenModifier)otherM;
        int cmp = V.CompareTo(other.V);
        if (cmp != 0)
            return cmp;
        cmp = T.CompareTo(other.T);
        return cmp != 0 ? cmp : -Forwards.CompareTo(other.Forwards);
    }

    public override string ToString() => 
        $"{V} / ε || {V} / {(Forwards ? (V.ToString() + T) : (T + V.ToString()))}";
}