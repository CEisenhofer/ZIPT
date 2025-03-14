#if false
using StringBreaker.Tokens;

namespace StringBreaker.Constraints.Modifier;

public class VarEpsilonModifier : ModifierBase {

    public StrVarToken Var { get; }

    public VarEpsilonModifier(StrVarToken var) => Var = var;

    public override void Apply(NielsenNode node) {
        var c = node.MkChild(node, this);
        node.AddOutgoing(this, c);
        foreach (var cnstr in c.AllStrConstraints) {
            cnstr.Apply(Var);
        }
    }

    protected override int CompareToInternal(ModifierBase otherM) => 
        ((VarEpsilonModifier)otherM).Var.CompareTo(Var);

    public override string ToString() => $"{Var} / ε";
}
#endif