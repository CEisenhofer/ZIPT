using System.Diagnostics;
using StringBreaker.Constraints.ConstraintElement;
using StringBreaker.IntUtils;
using StringBreaker.Tokens;

namespace StringBreaker.Constraints.Modifier;

public class EqSplitModifier : DirectedNielsenModifier {

    public StrEq Eq { get; }
    public int LhsIdx { get; }
    public int RhsIdx { get; }

    public EqSplitModifier(StrEq eq, int lhsIdx, int rhsIdx, bool forward) : base(forward) {
        Debug.Assert(lhsIdx >= 0);
        Debug.Assert(rhsIdx >= 0);
        Debug.Assert(lhsIdx < eq.LHS.Count);
        Debug.Assert(rhsIdx < eq.RHS.Count);
        Eq = eq;
        LhsIdx = lhsIdx;
        RhsIdx = rhsIdx;
    }

    public override void Apply(NielsenNode node) {
        Str lhs1 = new Str(Forwards ? LhsIdx : Eq.LHS.Count - LhsIdx);
        Str rhs1 = new Str(Forwards ? RhsIdx : Eq.RHS.Count - RhsIdx);
        Str lhs2 = new Str(!Forwards ? LhsIdx : Eq.LHS.Count - LhsIdx);
        Str rhs2 = new Str(!Forwards ? RhsIdx : Eq.RHS.Count - RhsIdx);
        for (int i = 0; i < LhsIdx; i++) {
            lhs1.Add(Eq.LHS.Peek(Forwards, i), !Forwards);
        }
        for (int i = LhsIdx; i < Eq.LHS.Count; i++) {
            lhs2.Add(Eq.LHS.Peek(Forwards, i), !Forwards);
        }
        for (int i = 0; i < RhsIdx; i++) {
            rhs1.Add(Eq.RHS.Peek(Forwards, i), !Forwards);
        }
        for (int i = RhsIdx; i < Eq.RHS.Count; i++) {
            rhs2.Add(Eq.RHS.Peek(Forwards, i), !Forwards);
        }

        var c = node.MkChild(node, []);
        c.RemoveConstraint(Eq);
        var eq1 = new StrEq(lhs1, rhs1);
        var eq2 = new StrEq(lhs2, rhs2);
        c.AddConstraints(eq1);
        c.AddConstraints(eq2);
        c.Parent!.SideConstraints.Add(eq1.Clone());
        c.Parent!.SideConstraints.Add(eq2.Clone());
    }

    protected override int CompareToInternal(ModifierBase otherM) {
        EqSplitModifier other = (EqSplitModifier)otherM;
        int cmp = Eq.CompareTo(other.Eq);
        if (cmp != 0)
            return cmp;
        cmp = LhsIdx.CompareTo(other.LhsIdx);
        if (cmp != 0)
            return cmp;
        cmp = RhsIdx.CompareTo(other.RhsIdx);
        return cmp != 0 ? cmp : Forwards.CompareTo(other.Forwards);
    }

    public override string ToString() =>
        $"{Eq} => {Eq}[{LhsIdx}, {RhsIdx}]";
}