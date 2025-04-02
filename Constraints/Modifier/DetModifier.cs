using StringBreaker.Constraints.ConstraintElement;
using StringBreaker.MiscUtils;

namespace StringBreaker.Constraints.Modifier;

public class DetModifier : ModifierBase {

    public List<Subst> Substitutions { get; } = [];
    public HashSet<Constraint> SideConstraints { get; } = [];
    public bool Trivial => Substitutions.IsEmpty() && SideConstraints.IsEmpty();
    public bool Success { get; set; }

    public override void Apply(NielsenNode node) {
        Success = SideConstraints.IsEmpty() || Substitutions.IsNonEmpty();
        var c = node.MkChild(node, Substitutions, true);
        foreach (var subst in Substitutions) {
            c.Apply(subst);
        }
        foreach (var cnstr in SideConstraints) {
            Success |= c.AddConstraints(cnstr);
            c.Parent!.SideConstraints.Add(cnstr.Clone());
        }
    }

    protected override int CompareToInternal(ModifierBase otherM) => 0;

    public override string ToString() =>
        string.Join(" && ", Substitutions.Select(s => s.ToString()).Concat(SideConstraints.Select(o => o.ToString())));
}