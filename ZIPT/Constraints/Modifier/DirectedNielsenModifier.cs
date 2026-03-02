namespace ZIPT.Constraints.Modifier;

public abstract class DirectedNielsenModifier : ModifierBase {
    public bool Forwards { get; }
    protected DirectedNielsenModifier(bool forwards, DependencyTracker reason) : base(reason) => Forwards = forwards;
}