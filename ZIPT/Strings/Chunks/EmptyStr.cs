using System.Diagnostics;
using ZIPT.Constraints;
using ZIPT.Strings.Tokens;

namespace ZIPT.Strings.Chunks;

public sealed class EmptyStr : Str {

    // this has to be 0 in order to be compositional (two structually different strings have the same hashcode)
    public const int HashCode = 0;

    public EmptyStr(uint id) : base(id) { }

    public override uint Length => 0;
    public override uint Level => 0;
    public override bool ContainsVar(NamedStrToken v) => false;
    public override void CollectVars(HashSet<NamedStrToken> contained) { }
    public override void CollectSymbols(NonTermSet nonTermSet, HashSet<CharToken> alphabet) { }

    public override Str Translate(StrManager manager) =>
        manager.EmptyStr;

    public override StrToken[] Sequence() => 
        Array.Empty<StrToken>();

    protected override int CompareToInternal(Str other) {
        Debug.Assert(ReferenceEquals(this, other));
        return 0;
    }

    public override bool Equals(Str? other) => other is EmptyStr;

    public override bool Equals(object? obj) => obj is EmptyStr;

    public override int GetHashCode() => HashCode;

    public override string RawString => "";
    public override string GetPlainString(NielsenGraph? graph) => "";
}