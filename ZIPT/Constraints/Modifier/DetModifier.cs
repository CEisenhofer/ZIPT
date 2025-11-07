using System.Diagnostics;
using ZIPT.Constraints.ConstraintElement;
using ZIPT.MiscUtils;

namespace ZIPT.Constraints.Modifier;

public class DetModifier : ModifierBase {

    //List<Subst> Substitutions { get; } = [];
    Subst? Substitution { get; set; }
    public HashSet<Constraint> SideConstraints { get; } = [];
    public bool Trivial => Substitution is null && SideConstraints.IsEmpty();

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

    public override IEnumerable<NielsenEdge> Apply(NielsenNode node) {
        Debug.Assert(SideConstraints.IsNonEmpty() || Substitution is not null);
        Debug.Assert(node.Outgoing.Count == 0);
        node.MkChild(node, 
            CollectionExtension.EmptyOrUnit(Substitution),
            SideConstraints, [],
            true);
        Debug.Assert(node.Outgoing.Count == 1);
        yield return node.Outgoing[0];
    }

    protected override int CompareToInternal(ModifierBase otherM) => 0;

    public override string ToString() =>
        string.Join(" && ", (Substitution is null
            ? Array.Empty<string>()
            : [Substitution.Value.ToString()]).Concat(SideConstraints.Select(o => o.ToString())));
}