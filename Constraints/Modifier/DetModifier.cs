using StringBreaker.Constraints.ConstraintElement;
using StringBreaker.MiscUtils;

namespace StringBreaker.Constraints.Modifier;

public class DetModifier : ModifierBase {

    //List<Subst> Substitutions { get; } = [];
    Subst? Substitution { get; set; }
    public HashSet<Constraint> SideConstraints { get; } = [];
    public bool Trivial => Substitution is null && SideConstraints.IsEmpty();
    public bool Success { get; set; }

    public void Add(Constraint cnstr) =>
        SideConstraints.Add(cnstr);

    public SimplifyResult Add(Subst s) {
        //if (Substitutions.Any(o => o.EqualKeys(s)))
        //    return SimplifyResult.Restart;
        //Substitutions.Add(s);
        if (Substitution is not null)
            return SimplifyResult.Restart;
        Substitution = s;
        return SimplifyResult.Proceed;
    }

    public override void Apply(NielsenNode node) {
        Success = SideConstraints.IsEmpty() || Substitution is not null;
        var c = node.MkChild(node, Substitution is null ? [] : [Substitution], true);
        if (Substitution is not null)
            c.Apply(Substitution);

        foreach (var cnstr in SideConstraints) {
            Success |= c.AddConstraints(cnstr);
            c.Parent!.SideConstraints.Add(cnstr.Clone());
        }
    }

    protected override int CompareToInternal(ModifierBase otherM) => 0;

    public override string ToString() =>
        string.Join(" && ", (Substitution is null ? Array.Empty<string>() : [Substitution.ToString()]).Concat(SideConstraints.Select(o => o.ToString())));
}