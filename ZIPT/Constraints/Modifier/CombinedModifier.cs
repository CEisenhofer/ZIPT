using System.Diagnostics;
using ZIPT.MiscUtils;

namespace ZIPT.Constraints.Modifier;

// Composite modifier that applies a sequence of modifiers in order; used to group several
// splitting/intro steps into a single logical choice.
public class CombinedModifier : ModifierBase {
    
    public ModifierBase[] Modifier { get; }

    public CombinedModifier(DependencyTracker reason, params ModifierBase[] modifier) : base(reason) {
        Debug.Assert(modifier.IsNonEmpty());
        Debug.Assert(modifier.All(o => o is not CombinedModifier));
        Modifier = modifier;
    }

    public override IEnumerable<NielsenEdge> Apply(LocalInfo info) {
        foreach (var modifier in Modifier) {
            foreach (var o in modifier.Apply(info))
                yield return o;
        }
        Debug.Assert(info.CurrentNode.Outgoing.Count == 1);
    }

    // CombinedModifier applies a sequence of modifiers sequentially producing their child edges.

    protected override int CompareToInternal(ModifierBase otherM) => 
        // This is dealt with in the non-internal version
        throw new NotSupportedException();

    public override string ToString() => 
        string.Join(" || ", Modifier.Select(o => o.ToString()));

    // Represent the combined modifier as concatenation of the sub-modifiers' string reprs.


}