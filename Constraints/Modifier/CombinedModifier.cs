using System.Diagnostics;
using StringBreaker.MiscUtils;

namespace StringBreaker.Constraints.Modifier;

public class CombinedModifier : ModifierBase {
    
    public ModifierBase[] Modifier { get; }

    public CombinedModifier(params ModifierBase[] modifier) {
        Debug.Assert(modifier.NonEmpty());
        Debug.Assert(modifier.All(o => o is not CombinedModifier));
        Modifier = modifier;
    }

    public override void Apply(NielsenNode node) {
        foreach (var modifier in Modifier) {
            modifier.Apply(node);
        }
    }

    protected override int CompareToInternal(ModifierBase otherM) => 
        // This is dealt with in the non-internal version
        throw new NotSupportedException();

    public override string ToString() => 
        string.Join(" || ", Modifier.Select(o => o.ToString()));


}