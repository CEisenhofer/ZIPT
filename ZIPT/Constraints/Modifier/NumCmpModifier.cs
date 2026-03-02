using System.Buffers;
using System.Numerics;
using ZIPT.Constraints.ConstraintElement;
using ZIPT.IntUtils;

namespace ZIPT.Constraints.Modifier;

public class NumCmpModifier : ModifierBase {

    public PDD<BigInteger> N1 { get; }
    public PDD<BigInteger> N2 { get; }

    public NumCmpModifier(PDD<BigInteger> n1, PDD<BigInteger> n2, DependencyTracker reason) : base(reason) {
        N1 = n1;
        N2 = n2;
    }

    public override IEnumerable<NielsenEdge> Apply(LocalInfo info) {
        // N1 < N2 (progress)
        // N2 <= N1 (progress)

        info.CurrentNode.MkChild(info, 
            [], [],
            [IntLe.MkLt(N1, N2, Reason)], [],
            true); // N1 < N2
        yield return info.CurrentNode.Outgoing[^1];
        info.CurrentNode.MkChild(info,
            [], [],
            [IntLe.MkLe(N2, N1, Reason)], [],
            true); // N2 <= N1
        yield return info.CurrentNode.Outgoing[^1];
    }

    protected override int CompareToInternal(ModifierBase otherM) {
        int cmp = N1.CompareTo(((NumCmpModifier)otherM).N1);
        return cmp != 0 ? cmp : N2.CompareTo(((NumCmpModifier)otherM).N2);
    }

    public override string ToString() => $"{N1} < {N2} || {N2} <= {N1}";
}