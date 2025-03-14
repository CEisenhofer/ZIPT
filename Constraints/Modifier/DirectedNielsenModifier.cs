namespace StringBreaker.Constraints.Modifier;

public abstract class DirectedNielsenModifier : ModifierBase {

    public bool Backwards { get; }

    protected DirectedNielsenModifier(bool backwards) => 
        Backwards = backwards;
}