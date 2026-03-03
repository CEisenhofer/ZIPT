using ZIPT.Constraints.ConstraintElement;
using ZIPT.Strings;
using ZIPT.Strings.Tokens;

namespace ZIPT.Constraints.Modifier;

public class ConstNielsenModifier : DirectedNielsenModifier {

    public StrVarToken V { get; }
    public StrToken T { get; }

    public ConstNielsenModifier(StrVarToken v, StrToken t, bool forward, DependencyTracker reason) : base(forward, reason) {
        V = v;
        T = t;
    }

    public override IEnumerable<NielsenEdge> Apply(LocalInfo info) {
        // Deterministic splitting of a variable into empty or `T+var` branches; used when a
        // token T (ground) is known to be a possible prefix.
        var subst = new Subst(V, info.Env.EmptyStr);
        info.CurrentNode.MkChild(info, [subst], [], [], [], true);
        yield return info.CurrentNode.Outgoing[^1];
        
        subst = new Subst(V, Forwards
            ? info.Env.MkString(T, V)
            : info.Env.MkString(V, T)
        );
        info.CurrentNode.MkChild(info, [subst], [], [], [], false);
        yield return info.CurrentNode.Outgoing[^1];
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