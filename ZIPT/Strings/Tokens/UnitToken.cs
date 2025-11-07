using ZIPT.Constraints;

namespace ZIPT.Strings.Tokens;

public abstract class UnitToken : StrToken {

    public override bool Nullable => false;
    public override bool BasicRegex => true;

    public sealed override List<StrDecomposition> GetDecomposition(NielsenNode node, bool fwd) =>
        // P(a) := {}
        [new StrDecomposition(node.Env.EmptyStr, node.Env.MkString(this), [], null)];
}