namespace ZIPT.Constraints.Modifier;

// Directed modifier base: carries a direction flag used by Nielsen splitting variants
// (forward vs backward processing of strings/regexes).
public abstract class DirectedNielsenModifier : ModifierBase {
    public bool Forwards { get; }
    protected DirectedNielsenModifier(bool forwards, DependencyTracker reason) : base(reason) => Forwards = forwards;
}
