using System.Diagnostics;
using StringBreaker.Constraints.ConstraintElement;
using StringBreaker.Tokens;

namespace StringBreaker.Constraints.Modifier;

public class SCharCharModifier : ModifierBase {

    public SymCharToken O { get; }
    public UnitToken C { get; }
    public SCharCharModifier(SymCharToken o, UnitToken c) {
        O = o;
        C = c;
    }

    public override void Apply(NielsenNode node) {
        // O / U (progress)
        // O != U (progress)
        var c = node.MkChild(node, [new SubstSChar(O, C)], Array.Empty<Constraint>(), Array.Empty<DisEq>(), true);
        node.MkChild(node, Array.Empty<Subst>(), Array.Empty<Constraint>(), [new DisEq(O, C)], true);
    }

    protected override int CompareToInternal(ModifierBase otherM) {
        SCharCharModifier other = (SCharCharModifier)otherM;
        int cmp = O.CompareTo(other.O);
        return cmp != 0 ? cmp : C.CompareTo(other.C);
    }

    public override string ToString() => 
        $"{O} / {C} || {O} != {C}";
}