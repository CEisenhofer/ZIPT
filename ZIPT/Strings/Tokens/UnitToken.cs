using ZIPT.Constraints;
using ZIPT.Constraints.ConstraintElement;
using ZIPT.Strings.Chunks;

namespace ZIPT.Strings.Tokens;

public abstract class UnitToken : StrToken {

    public sealed override bool IsNullable(NielsenNode node) => false;

    public sealed override List<PrefixDecomposition> GetPrefixes(NielsenNode node, bool fwd) =>
        // P(a) := {}
        [new PrefixDecomposition(node.Env.EmptyStr, [], null)];
}