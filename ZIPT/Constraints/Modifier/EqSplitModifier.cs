using System.Diagnostics;
using ZIPT.Constraints.ConstraintElement;
using ZIPT.IntUtils;
using ZIPT.Strings;
using ZIPT.Strings.Chunks;
using ZIPT.Strings.Tokens;

namespace ZIPT.Constraints.Modifier;

public class EqSplitModifier : DirectedNielsenModifier {

    public StrEq Eq { get; }
    public uint LhsIdx { get; }
    public uint RhsIdx { get; }
    public int Padding { get; }

    public EqSplitModifier(StrEq eq, uint lhsIdx, uint rhsIdx, int padding, bool forward) : base(forward) {
        Debug.Assert(lhsIdx <= eq.LHS.Length);
        Debug.Assert(rhsIdx <= eq.RHS.Length);
        Debug.Assert(lhsIdx < eq.LHS.Length || rhsIdx < eq.RHS.Length);
        Eq = eq;
        LhsIdx = lhsIdx;
        RhsIdx = rhsIdx;
        Padding = padding;
    }

    public override void Apply(NielsenNode node) {
        Debug.Assert(LhsIdx <= Eq.LHS.Length);
        Debug.Assert(RhsIdx <= Eq.RHS.Length);
        Debug.Assert(LhsIdx < Eq.LHS.Length || RhsIdx < Eq.RHS.Length);

        // Eq.LHS[0..LhsIdx] [Padding] = Eq.RHS[0..RhsIdx] && Eq.LHS[LhsIdx..] = [Padding] Eq.RHS[RhsIdx..] (progress)
        // TODO: Add a split function for strings
        Str lhs1 = node.Env.StrManager.Extract(Eq.LHS, LhsIdx, Forwards);
        Str rhs1 = node.Env.StrManager.Extract(Eq.RHS, LhsIdx, !Forwards);
        Str lhs2 = node.Env.StrManager.Extract(Eq.LHS, LhsIdx, Forwards);
        Str rhs2 = node.Env.StrManager.Extract(Eq.RHS, LhsIdx, !Forwards);

        var padVar = node.Env.GetOrCreateStrVar("o");
        if (Padding > 0) {
            lhs2 = node.Env.StrManager.Concat(lhs2, padVar, Forwards);
            rhs1 = node.Env.StrManager.Concat(padVar, rhs1, Forwards);
        }
        else if (Padding < 0) {
            lhs1 = node.Env.StrManager.Concat(lhs1, padVar, Forwards);
            rhs2 = node.Env.StrManager.Concat(padVar, rhs2, Forwards);
        }

        var eq1 = new StrEq(lhs1, rhs1);
        var eq2 = new StrEq(lhs2, rhs2);
        IntEq fixedEq = new IntEq(LenVar.MkLenPoly(padVar, node.Env), node.Env.IntPDDManager.MkPDD(Math.Abs(Padding)));
        IntEq iEq1 = new IntEq(LenVar.MkLenPoly(lhs1, node.Env), LenVar.MkLenPoly(rhs1, node.Env));
        IntEq iEq2 = new IntEq(LenVar.MkLenPoly(lhs2, node.Env), LenVar.MkLenPoly(rhs2, node.Env));
        List<Constraint> cnstr = [eq1, eq2, fixedEq];
        if (!iEq1.Poly.IsZero)
            cnstr.Add(iEq1);
        if (!iEq2.Poly.IsZero)
            cnstr.Add(iEq2);
        NielsenNode c = node.MkChild(node, Array.Empty<Subst>(), cnstr, true);
        c.RemoveStrEq(Eq);
    }

    protected override int CompareToInternal(ModifierBase otherM) {
        EqSplitModifier other = (EqSplitModifier)otherM;
        int cmp = Eq.CompareTo(other.Eq);
        if (cmp != 0)
            return cmp;
        cmp = Math.Abs(Padding).CompareTo(Math.Abs(other.Padding));
        if (cmp != 0)
            return cmp;
        cmp = LhsIdx.CompareTo(other.LhsIdx);
        if (cmp != 0)
            return cmp;
        cmp = RhsIdx.CompareTo(other.RhsIdx);
        if (cmp != 0)
            return cmp;
        if (Padding < 0 != other.Padding < 0)
            return Padding < 0 ? 1 : -1;
        return Forwards.CompareTo(other.Forwards);
    }

    public override string ToString() =>
        $"{Eq} => {Eq}[{LhsIdx}, {RhsIdx}] - {Padding}/{Forwards}";
}