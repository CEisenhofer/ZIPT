using System.Diagnostics;
using ZIPT.Constraints.ConstraintElement;
using ZIPT.IntUtils;
using ZIPT.Tokens;

namespace ZIPT.Constraints.Modifier;

public class EqSplitModifier : DirectedNielsenModifier {

    public StrEq Eq { get; }
    public int LhsIdx { get; }
    public int RhsIdx { get; }
    public int Padding { get; }

    public EqSplitModifier(StrEq eq, int lhsIdx, int rhsIdx, int padding, bool forward) : base(forward) {
        Debug.Assert(lhsIdx >= 0);
        Debug.Assert(rhsIdx >= 0);
        Debug.Assert(lhsIdx <= eq.LHS.Count);
        Debug.Assert(rhsIdx <= eq.RHS.Count);
        Debug.Assert(lhsIdx < eq.LHS.Count || rhsIdx < eq.RHS.Count);
        Eq = eq;
        LhsIdx = lhsIdx;
        RhsIdx = rhsIdx;
        Padding = padding;
    }

    public override void Apply(NielsenNode node) {
        Debug.Assert(LhsIdx >= 0);
        Debug.Assert(RhsIdx >= 0);
        Debug.Assert(LhsIdx <= Eq.LHS.Count);
        Debug.Assert(RhsIdx <= Eq.RHS.Count);
        Debug.Assert(LhsIdx < Eq.LHS.Count || RhsIdx < Eq.RHS.Count);

        // Eq.LHS[0..LhsIdx] [Padding] = Eq.RHS[0..RhsIdx] && Eq.LHS[LhsIdx..] = [Padding] Eq.RHS[RhsIdx..] (progress)
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

        SymCharToken[] ch;
        if (Padding > 0) {
            int p = Padding;
            ch = new SymCharToken[p];
            for (int i = 0; i < p; i++) {
                ch[i] = new SymCharToken();
                rhs1.Add(ch[i], !Forwards);
            }
            for (int i = 0; i < p; i++) {
                lhs2.Add(ch[p - i - 1], Forwards);
            }
        }
        else if (Padding < 0) {
            int p = -Padding;
            ch = new SymCharToken[p];
            for (int i = 0; i < p; i++) {
                ch[i] = new SymCharToken();
                lhs1.Add(ch[i], !Forwards);
            }
            for (int i = 0; i < p; i++) {
                rhs2.Add(ch[p - i - 1], Forwards);
            }
        }

        var eq1 = new StrEq(lhs1, rhs1);
        var eq2 = new StrEq(lhs2, rhs2);
        IntEq iEq1 = new IntEq(LenVar.MkLenPoly(lhs1), LenVar.MkLenPoly(rhs1));
        IntEq iEq2 = new IntEq(LenVar.MkLenPoly(lhs2), LenVar.MkLenPoly(rhs2));
        List<Constraint> cnstr = [eq1, eq2];
        if (!iEq1.Poly.IsZero)
            cnstr.Add(iEq1);
        if (!iEq2.Poly.IsZero)
            cnstr.Add(iEq2);
        NielsenNode c = node.MkChild(node, Array.Empty<Subst>(), cnstr, Array.Empty<DisEq>(), true);
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