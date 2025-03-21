using StringBreaker.Tokens;

namespace StringBreaker.Constraints.Modifier;

public class ConstNielsenModifier : DirectedNielsenModifier {

    public StrVarToken Var { get; }
    public StrToken Prefix { get; }

    public ConstNielsenModifier(StrVarToken var, StrToken pr, bool forward) : base(forward) {
        Var = var;
        Prefix = pr;
    }

    public override void Apply(NielsenNode node) {
        var subst = new SubstVar(Var);
        var c = node.MkChild(node, [subst]);
        foreach (var cnstr in c.AllConstraints) {
            cnstr.Apply(subst);
        }
        subst = new SubstVar(Var, Forwards ? [Prefix, Var] : [Var, Prefix]);
        c = node.MkChild(node, [subst]);
        foreach (var cnstr in c.AllConstraints) {
            cnstr.Apply(subst);
        }
    }

    protected override int CompareToInternal(ModifierBase otherM) {
        ConstNielsenModifier other = (ConstNielsenModifier)otherM;
        int cmp = Forwards.CompareTo(other.Forwards);
        if (cmp != 0)
            return cmp;
        cmp = Var.CompareTo(other.Var);
        return cmp != 0 ? cmp : Prefix.CompareTo(other.Prefix);
    }

    public override string ToString() => 
        $"{Var} / ε || {Var} / {(Forwards ? (Var.ToString() + Prefix) : (Prefix + Var.ToString()))}";
}