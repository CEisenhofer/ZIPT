using System.Diagnostics;
using ZIPT.Constraints.ConstraintElement;
using ZIPT.MiscUtils;

namespace ZIPT.Constraints.Modifier;

public class DetModifier : ModifierBase {

    Subst? Substitution { get; set; }
    CharSubst? SubstitutionC { get; set; }
    public HashSet<Constraint> SideConstraints { get; } = [];
    public bool Trivial => Substitution is null && SubstitutionC is null && SideConstraints.IsEmpty();

    public DetModifier() : base(new DependencyTracker(0)) { }

    public void Add(Constraint cnstr) =>
        SideConstraints.Add(cnstr);

    public void AddRewritten(Constraint cnstr, NielsenNode node) {
        if (Substitution.HasValue)
            SideConstraints.Add(cnstr.Apply(Substitution.Value, node));
        else if (SubstitutionC.HasValue)
            SideConstraints.Add(cnstr.Apply(SubstitutionC.Value, node));
        else
            Add(cnstr);
    }

    public bool Add(Subst s) {
        if (Substitution is not null && !Substitution.Equals(s))
            return false;
        if (SubstitutionC is not null)
            return false;
        Substitution = s;
        return true;
    }

    public bool Add(CharSubst s) {
        if (SubstitutionC is not null && !SubstitutionC.Equals(s))
            return false;
        if (Substitution is not null)
            return false;
        SubstitutionC = s;
        return true;
    }

    public override IEnumerable<NielsenEdge> Apply(LocalInfo info) {
        Debug.Assert(SideConstraints.IsNonEmpty() || Substitution is not null || SubstitutionC is not null);
        return [ForceApply(info)];
    }

    public NielsenEdge ForceApply(LocalInfo info) {
        Debug.Assert(info.CurrentNode.Outgoing.Count == 0);
        info.CurrentNode.MkChild(info, 
            CollectionExtension.EmptyOrUnit(Substitution), CollectionExtension.EmptyOrUnit(SubstitutionC),
            SideConstraints, [],
            true);
        Debug.Assert(info.CurrentNode.Outgoing.Count == 1);
        return info.CurrentNode.Outgoing[0];
    }

    protected override int CompareToInternal(ModifierBase otherM) => 0;

    public override string ToString() {
        List<string> parts = [];
        if (Substitution is not null)
            parts.Add(Substitution.Value.ToString());
        if (SubstitutionC is not null)
            parts.Add(SubstitutionC.Value.ToString());
        parts.AddRange(SideConstraints.Select(o => o.ToString()));
        return string.Join(" && ", parts);
    }
}