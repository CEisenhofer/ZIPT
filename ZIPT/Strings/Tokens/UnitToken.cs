using ZIPT.Constraints;

namespace ZIPT.Strings.Tokens;

public abstract class UnitToken : StrToken {

    public sealed override bool Ground => true;
    public sealed override bool IsNullable(NielsenNode node) => false;
}