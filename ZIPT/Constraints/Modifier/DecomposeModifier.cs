using System.Diagnostics;
using ZIPT.Constraints.ConstraintElement;
using ZIPT.MiscUtils;
using ZIPT.Strings.Chunks;
using ZIPT.Strings.Tokens;
using ZIPT.Strings.Tokens.RegexTokens;

namespace ZIPT.Constraints.Modifier;

public class DecomposeModifier : ModifierBase {
    public StrMem Mem { get; }

    // Forward only for now
    public DecomposeModifier(StrMem mem) {
        Debug.Assert(mem.Str.IsNonEmpty());
        Debug.Assert(mem.Str.First is NamedStrToken or PowerToken);
        Mem = mem;
    }

    public override IEnumerable<NielsenEdge> Apply(NielsenNode node) {
        // Do the decomposition of tu into
        // prefix + postfix = r
        // t \in prefix
        // u \in postfix
        var prefix = new PreToken((uint)node.Id);
        var postfix = new PostToken((uint)node.Id);
        var splitConstraint = new ReSplit(Mem.Regex, prefix, postfix);
        var m1 = new StrMem(node.Env.MkString(Mem.Str.First), node.Env.MkString(prefix));
        var m2 = new StrMem(node.Env.StrManager.DropLeft(Mem.Str), node.Env.MkString(postfix));
        node.MkChild(node, [], [m1, m2, splitConstraint], [Mem], true);
        yield return node.Outgoing[^1];
    }

    protected override int CompareToInternal(ModifierBase otherM) {
        DecomposeModifier other = (DecomposeModifier)otherM;
        return Mem.CompareTo(other.Mem);
    }

    public override string ToString() => 
        $"Decompose({Mem})";
}
