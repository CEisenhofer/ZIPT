using StringBreaker.Constraints.ConstraintElement;
using StringBreaker.MiscUtils;

namespace StringBreaker.Constraints.Modifier;

public class DetModifier : ModifierBase {

    public List<Subst> Substitutions { get; } = [];
    public HashSet<Constraint> SideConstraints { get; } = [];
    public bool Trivial => Substitutions.IsEmpty() && SideConstraints.IsEmpty();

    public override void Apply(NielsenNode node) {
        var c = node.MkChild(node, Substitutions);
        foreach (var subst in Substitutions) {
            foreach (var cnstr in c.AllStrConstraints) {
                cnstr.Apply(subst);
            }
        }
        foreach (var cnstr in SideConstraints) {
            c.AddConstraints(cnstr);
            c.Parent!.SideConstraints.Add(cnstr.Clone());
        }
    }

    protected override int CompareToInternal(ModifierBase otherM) => 0;

    public override string ToString() =>
        string.Join(" && ", Substitutions.Select(s => s.ToString()).Concat(SideConstraints.Select(o => o.ToString())));
}