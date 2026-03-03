using ZIPT.Constraints;

namespace ZIPT.Strings.Tokens;

// Base class for tokens that represent a single atomic unit (characters, sets, symbolic chars).
// These tokens are non-nullable and yield a simple decomposition for splitting.
public abstract class UnitToken : StrToken {

    public override bool Nullable => false;
    public override bool BasicRegex => true;

    public sealed override List<StrDecomposition> GetDecomposition(NielsenNode node, bool fwd) =>
        // P(a) := {}
        [new StrDecomposition(node.Env.EmptyStr, node.Env.MkString(this), [], null)];
}
