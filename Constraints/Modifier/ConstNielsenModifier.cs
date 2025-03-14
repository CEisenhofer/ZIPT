using StringBreaker.Tokens;

namespace StringBreaker.Constraints.Modifier;

public class ConstNielsenModifier : DirectedNielsenModifier {

    public StrVarToken Var { get; }
    public StrToken Prefix { get; }

    public ConstNielsenModifier(StrVarToken var, StrToken pr, bool backward) : base(backward) {
        Var = var;
        Prefix = pr;
    }

    public override void Apply(NielsenNode node) {
        var subst = new Subst(Var);
        var c = node.MkChild(node, [subst]);
        foreach (var cnstr in c.AllStrConstraints) {
            cnstr.Apply(subst);
        }
        subst = new Subst(Var, Backwards ? [Var, Prefix] : [Prefix, Var]);
        c = node.MkChild(node, [subst]);
        foreach (var cnstr in c.AllStrConstraints) {
            cnstr.Apply(subst);
        }
    }

    protected override int CompareToInternal(ModifierBase otherM) {
        ConstNielsenModifier other = (ConstNielsenModifier)otherM;
        int cmp = Backwards.CompareTo(other.Backwards);
        if (cmp != 0)
            return cmp;
        cmp = Var.CompareTo(other.Var);
        return cmp != 0 ? cmp : Prefix.CompareTo(other.Prefix);
    }

    public override string ToString() => 
        $"{Var} / ε || {Var} / {(Backwards ? (Prefix + Var.ToString()) : (Var.ToString() + Prefix))}";
}