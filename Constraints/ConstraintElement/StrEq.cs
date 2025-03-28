using System.Diagnostics;
using Microsoft.Z3;
using StringBreaker.Constraints.ConstraintElement.AuxConstraints;
using StringBreaker.Constraints.Modifier;
using StringBreaker.IntUtils;
using StringBreaker.MiscUtils;
using StringBreaker.Tokens;

namespace StringBreaker.Constraints.ConstraintElement;

public sealed class StrEq : StrEqBase {

    public StrEq(Str lhs, Str rhs) : base(lhs, rhs) { }
    public StrEq(Str empty) : base([], empty) { }

    public override StrEq Clone() => 
        new(LHS.Clone(), RHS.Clone());

    // Minimal order: The smallest token is front-most.
    // If there are multiple equal ones, the one after is smaller than all the ones in front of the other candidates and so on...
    // the order is always LHS to RHS (no matter in which direction we reduce)
    static int GetMinimalOrder(Str s) {

        StrToken LookAhead(int i, int l) => 
            s[(i + l) % s.Count];

        Debug.Assert(s.IsNonEmpty());
        List<int> candidates = Enumerable.Range(0, s.Count).ToList();
        List<int> newCandidates = [];

        for (int i = 0; candidates.Count != 1 && i < s.Count; i++) {
            StrToken min = LookAhead(candidates[0], i);
            newCandidates.Add(candidates[0]);
            Debug.Assert(candidates.IsNonEmpty());
            for (var j = 1; j < candidates.Count; j++) {
                var current = LookAhead(candidates[j], i);
                int cmp = min.CompareTo(current);
                switch (cmp) {
                    case 0:
                        newCandidates.Add(candidates[j]);
                        break;
                    case > 0:
                        newCandidates.Clear();
                        newCandidates.Add(candidates[j]);
                        min = current;
                        break;
                }
            }
            (newCandidates, candidates) = (candidates, newCandidates);
            newCandidates.Clear();
        }

        Debug.Assert(candidates.IsNonEmpty()); // this can be violated if we have e.g., (aa)^n but this should be simplified away anyway...
        return candidates[0];
    }

    static SimplifyResult SimplifyEmpty(IEnumerable<StrToken> s, NielsenNode node, List<Subst> newSubst, HashSet<Constraint> newSideConstr) {
        foreach (var t in s) {
            if (t is UnitToken)
                return SimplifyResult.Conflict;
            if (t is StrVarToken v)
                newSubst.Add(new SubstVar(v));
            else if (t is PowerToken p) {
                if (node.IsLt(new Poly(), p.Power))
                    // p.Power > 0
                    newSideConstr.Add(new StrEq(p.Base));
                else if (!p.Base.IsNullable(node))
                    // p.Base != ""
                    newSideConstr.Add(new IntEq(p.Power));
            }
            else
                throw new NotSupportedException();
        }
        return SimplifyResult.Proceed;
    }

    // Try to add the substitution: x / s ==> do an occurrence check. If it fails, we have to add it as an ordinary equation
    public void AddDefinition(StrVarToken v, Str s, NielsenNode node, List<Subst> newSubst, HashSet<Constraint> newSideConstr) {
        if (s.RecursiveIn(v))
            // newSideConstr.Add(new StrEq([v], s));
            return;
        newSubst.Add(new SubstVar(v, s));
    }

    SimplifyResult SimplifyDir(NielsenNode node, List<Subst> newSubst, HashSet<Constraint> newSideConstr, bool dir) {
        // This can cause problems, as it might unwind/compress the beginning/end over and over again (might even detect it as subsumed)
        var s1 = LHS;
        var s2 = RHS;
        SortStr(ref s1, ref s2, dir);
        while (LHS.IsNonEmpty() && RHS.IsNonEmpty()) {
            SortStr(ref s1, ref s2, dir);
            Debug.Assert(s1.Count > 0);
            Debug.Assert(s2.Count > 0);

            if (SimplifySame(s1, s2, dir))
                continue;

            var t1 = s1.Peek(dir);
            var t2 = s2.Peek(dir);

            if (t1 is UnitToken u1 && t2 is UnitToken u2 && node.AreDiseq(u1, u2))
                return SimplifyResult.Conflict;

            if (t1 is SymCharToken sc1) {
                if (t2 is UnitToken u) {
                    newSubst.Add(new SubstSChar(sc1, u));
                    return SimplifyResult.Proceed;
                }
            }

            if (t1 is PowerToken p1) {
                if (node.IsZero(p1.Power)) {
                    s1.Drop(dir);
                    continue;
                }
                if (!IsPrefixConsistent(node, p1.Base, s2, dir)) {
                    newSideConstr.Add(new IntEq(new Poly(), p1.Power));
                    return SimplifyResult.Proceed;
                }
            }
            if (t2 is PowerToken p2) {
                if (node.IsZero(p2.Power)) {
                    s2.Drop(dir);
                    continue;
                }
                if (!IsPrefixConsistent(node, p2.Base, s1, dir)) {
                    newSideConstr.Add(new IntEq(new Poly(), p2.Power));
                    return SimplifyResult.Proceed;
                }
            }

            if (SimplifyPower(node, s1, s2, dir))
                continue;
            break;
        }
        return SimplifyResult.Proceed;
    }

    static int simplifyCount;

    protected override SimplifyResult SimplifyInternal(NielsenNode node, 
        List<Subst> newSubst, HashSet<Constraint> newSideConstr, 
        ref BacktrackReasons reason) {
        simplifyCount++;
        Log.WriteLine($"Simplify Eq ({simplifyCount}): {LHS} = {RHS}");
        LHS = LcpCompression(LHS) ?? LHS;
        RHS = LcpCompression(RHS) ?? RHS;
        if (SimplifyDir(node, newSubst, newSideConstr, true) == SimplifyResult.Conflict) {
            reason = BacktrackReasons.SymbolClash;
            return SimplifyResult.Conflict;
        }
        if (SimplifyDir(node, newSubst, newSideConstr, false) == SimplifyResult.Conflict) {
            reason = BacktrackReasons.SymbolClash;
            return SimplifyResult.Conflict;
        }

        if (LHS.IsEmpty() && RHS.IsEmpty())
            return SimplifyResult.Satisfied;

        if (LHS.IsEmpty() || RHS.IsEmpty()) {
            var eq = LHS.IsEmpty() ? RHS : LHS;
            // Remove powers that actually do not exist anymore
            while (eq.IsNonEmpty() && eq.Peek(true) is PowerToken p) {
                Str? s;
                if ((s = SimplifyPowerSingle(node, p)) is not null) {
                    eq.Drop(true);
                    eq.AddRange(s, true);
                    continue;
                }
                break;
            }
            if (eq.IsEmpty())
                return SimplifyResult.Satisfied;
            if (SimplifyEmpty(eq, node, newSubst, newSideConstr) == SimplifyResult.Conflict) {
                reason = BacktrackReasons.SymbolClash;
                return SimplifyResult.Conflict;
            }
            SortStr();
            return SimplifyResult.Proceed;
        }

        // TODO: Generalize for powers!
        // Check Multiset abstraction
        var lhsSet = LHS.ToSet();
        var rhsSet = RHS.ToSet();
        MSet<StrToken>.ElimCommon(lhsSet, rhsSet);
        if (lhsSet.IsEmpty() != rhsSet.IsEmpty()) {
            var nonEmpty = lhsSet.IsEmpty() ? rhsSet : lhsSet;
            // Remove powers that actually do not exist anymore
            while (nonEmpty.IsNonEmpty() && nonEmpty.First().t is PowerToken p) {
                Str? s;
                if ((s = SimplifyPowerSingle(node, p)) is not null) {
                    nonEmpty.RemoveAll(p);
                    nonEmpty.Add(s);
                    continue;
                }
                break;
            }
            if (SimplifyEmpty(nonEmpty.Keys, node, newSubst, newSideConstr) == SimplifyResult.Conflict) {
                reason = BacktrackReasons.ParikhImage;
                return SimplifyResult.Conflict;
            }
            SortStr();
            return SimplifyResult.Proceed;
        }
        // Propagate assignments

        if (LHS is [StrVarToken] || RHS is [StrVarToken]) {
            var (v, s) = LHS is [StrVarToken] ? ((StrVarToken)LHS[0], RHS) : ((StrVarToken)RHS[0], LHS);
            // important: clone it; otherwise one might into endless recursions when applied to itself
            AddDefinition(v, s, node, newSubst, newSideConstr);
        }
        SortStr();
        return SimplifyResult.Proceed;
    }

    NumCmpModifier? SplitPowerElim(StrToken t, Str s, bool dir) {
        if (t is not PowerToken p1)
            return null;
        var r = CommPower(p1.Base, s, dir);
        return r.idx > 0 ? new NumCmpModifier(p1.Power, r.num) : null;
    }

    NumUnwindingModifier? SplitPowerUnwind(StrToken t, bool varInvolved) => 
        t is not PowerToken p ? null : (varInvolved ? new VarNumUnwindingModifier(p.Power) : new ConstNumUnwindingModifier(p.Power));

    Str? TryGetPowerSplitBase(StrVarToken v, Str s, bool dir) {
        if (s.IsEmpty())
            return null;
        var i = 0;
        for (; i < s.Count && !s.Peek(dir, i).Equals(v); i++) { }

        if (i >= s.Count)
            // Non-rec Case
            return null;
        // Rec Case
        Debug.Assert(s.Peek(dir, i).Equals(v));
        return dir 
            ? new Str(s.Take(i).ToList()) 
            : new Str(s.Reverse().Take(i).Reverse().ToList());
    }

    ModifierBase? SplitEq(Str s1, Str s2, bool dir) {
        if (s1.IsEmpty() || s2.IsEmpty())
            return null;
        // TODO: This is not optimal!
        Len constDiff = 0;
        Len best = Len.PosInf;
        int bestLhs = 0, bestRhs = 0;
        Poly lhs = new(), rhs = new();
        int lhsIdx = 0; int rhsIdx = 0;
        while (lhsIdx < s1.Count || rhsIdx < s2.Count) {
            if (lhsIdx > 0 || rhsIdx > 0) {
                if (lhs.IsZero && rhs.IsZero) {
                    if (constDiff.Abs() < best) {
                        best = constDiff;
                        bestLhs = lhsIdx;
                        bestRhs = rhsIdx;
                    }
                    if (constDiff.IsZero)
                        return new EqSplitModifier(this, bestLhs, bestRhs, dir);
                }
            }
            Poly len;
            if (lhs.IsEmpty() && rhs.IsNonEmpty() ||
                (lhs.IsEmpty() && rhs.IsEmpty() && constDiff.IsNeg)) {

                if (s1.Count <= lhsIdx)
                    break;
                len = LenVar.MkLenPoly([s1.Peek(dir, lhsIdx++)]);
                constDiff += len.ConstPart;
                len.ElimConst();
                if (!len.IsZero) {
                    lhs.Plus(len);
                    Poly.ElimCommon(lhs, rhs);
                }
                continue;
            }
            if (s2.Count <= rhsIdx)
                break;
            len = LenVar.MkLenPoly([s2.Peek(dir, rhsIdx++)]);
            constDiff -= len.ConstPart;
            len.ElimConst();
            if (!len.IsZero) {
                rhs.Plus(len);
                Poly.ElimCommon(lhs, rhs);
            }
        }
        if (best.IsInf)
            return null;
        Debug.Assert(!best.IsZero);
        if (best.IsNeg) {
            // split left
            if (bestLhs <= 0 || bestLhs >= s1.Count || s1.Peek(dir, bestLhs - 1) is not StrVarToken v1 || !best.TryGetInt(out int val1))
                return null;
            return new VarPaddingModifier(v1, -val1, !dir);
        }
        if (bestRhs <= 0 || bestRhs >= s2.Count || s2.Peek(dir, bestRhs - 1) is not StrVarToken v2 || !best.TryGetInt(out int val2))
            return null;
        return new VarPaddingModifier(v2, val2, !dir);
    }

    ModifierBase? SplitVarVar(Str s1, Str s2, bool dir) {
        if (s1.IsEmpty() || s2.IsEmpty() || s1.Peek(dir) is not StrVarToken v1 || s2.Peek(dir) is not StrVarToken v2)
            return null;

        Str? p1 = TryGetPowerSplitBase(v1, s2, dir);
        Str? p2 = TryGetPowerSplitBase(v2, s1, dir);
        if (p1 is not null && p2 is not null) {
            if (p1.Ground && p2.Ground) {
                Debug.Assert(false); // How could that happen?!
                return new GPowerGPowerIntrModifier(v1, v2, p1, p2, dir);
            }
            if (p1.Ground)
                return new CombinedModifier(
                    new GPowerIntrModifier(v1, p1, dir),
                    new ConstNielsenModifier(v2, v1, dir)
                );
            //return new GPowerPowerIntrModifier(v1, v2, p1, p2, dir);
            if (p2.Ground)
                return new CombinedModifier(
                    new GPowerIntrModifier(v2, p2, dir),
                    new ConstNielsenModifier(v1, v2, dir)
                );
            // return new GPowerPowerIntrModifier(v2, v1, p2, p1, dir);
            return
                new VarNielsenModifier(v1, v2, dir);
            //return new PowerPowerIntrModifier(v1, v2, p1, p2, dir);
        }
        if (p1 is not null) {
            (p1, p2) = (p2, p1);
            (v1, v2) = (v2, v1);
            (s1, s2) = (s2, s1);
        }
        if (p1 is null)
            return new VarNielsenModifier(v1, v2, dir);
        if (p1.Ground)
            return new GPowerIntrConstNielsen(v1, v2, p1, dir);
        return new PowerIntrConstNielsen(v1, v2, p1, dir);
    }

    ModifierBase? SplitGroundPower(StrToken t, Str s, bool dir) {
        if (t is not StrVarToken v || s.IsEmpty() || s.Peek(dir) is not UnitToken)
            return null;
        Str? p = TryGetPowerSplitBase(v, s, dir);
        if (p is not null && p.Ground)
            return new GPowerIntrModifier(v, p, dir);
        return null;
    }

    ModifierBase? SplitVarChar(StrToken t, Str s, bool dir) {
        if (t is not StrVarToken v || s.IsEmpty() || s.Peek(dir) is not UnitToken)
            return null;
        Str? p = TryGetPowerSplitBase(v, s, dir);
        if (p is null)
            return new ConstNielsenModifier(v, s.Peek(dir), dir);
        if (p.Ground) {
            Debug.Assert(false); // This should be excluded before (SplitGroundPower)
            return new GPowerIntrModifier(v, p, dir);
        }
        return new ConstNielsenModifier(v, s.Peek(dir), dir);
        //return new PowerIntrModifier(v, p, dir);
    }

    ModifierBase? SplitVarPower(StrToken t, Str s, bool dir) {
        if (t is not StrVarToken v || s.IsEmpty() || s.Peek(dir) is not PowerToken { Ground: true } p)
            return null;

        Str? b = TryGetPowerSplitBase(v, s, dir);
        if (b is null)
            return new PowerSplitModifier(v, p, dir);
        if (b.Ground)
            return new GPowerIntrModifier(v, b, dir);
        return new PowerSplitModifier(v, p, dir);
    }

    ModifierBase ExtendDir(bool dir) {
        Str s1 = LHS;
        Str s2 = RHS;
        SortStr(ref s1, ref s2, dir);
        if (s1.IsEmpty()) {
            Debug.Assert(!s2.IsEmpty());
            foreach (var s in s2) {
                if (s is PowerToken p)
                    return new PowerEpsilonModifier(p);
                // Simplify step should have already dealt with everything else!
                throw new NotSupportedException();
            }
            throw new NotSupportedException();
        }
        Debug.Assert(!s1.IsEmpty() && !s2.IsEmpty());

        var t1 = s1.Peek(dir);
        var t2 = s2.Peek(dir);

        ModifierBase? ret;

        if ((ret = SplitPowerElim(t1, s2, dir)) is not null)
            return ret;
        if ((ret = SplitPowerElim(t2, s1, dir)) is not null)
            return ret;
        if (t2 is not NamedStrToken && (ret = SplitPowerUnwind(t1, false)) is not null)
            return ret;
        if (t1 is not NamedStrToken && (ret = SplitPowerUnwind(t2, false)) is not null)
            return ret;
        if ((ret = SplitGroundPower(t1, s2, dir)) is not null)
            return ret;
        if ((ret = SplitGroundPower(t2, s1, dir)) is not null)
            return ret;
        if ((ret = SplitEq(s1, s2, dir)) is not null)
            return ret;
        if ((ret = SplitVarPower(t1, s2, dir)) is not null)
            return ret;
        if ((ret = SplitVarPower(t2, s1, dir)) is not null)
            return ret;
        if ((ret = SplitVarChar(t1, s2, dir)) is not null)
            return ret;
        if ((ret = SplitVarChar(t2, s1, dir)) is not null)
            return ret;
        if ((ret = SplitVarVar(s1, s2, dir)) is not null)
            return ret;
        if ((ret = SplitPowerUnwind(t1, true)) is not null)
            return ret;
        if ((ret = SplitPowerUnwind(t2, true)) is not null)
            return ret;
        throw new NotSupportedException();
    }

    public override ModifierBase Extend(NielsenNode node) {
        var m1 = ExtendDir(true);
        var m2 = ExtendDir(false);
        return m1.CompareTo(m2) <= 0 ? m1 : m2;
    }

    public override int CompareToInternal(StrConstraint other) {
        StrEq otherEq = (StrEq)other;
        int cmp = LHS.Count.CompareTo(otherEq.LHS.Count);
        if (cmp != 0)
            return cmp;
        cmp = RHS.Count.CompareTo(otherEq.RHS.Count);
        if (cmp != 0)
            return cmp;
        cmp = LHS.CompareTo(otherEq.LHS);
        return cmp != 0 ? cmp : RHS.CompareTo(otherEq.RHS);
    }

    public override StrConstraint Negate() => 
        new StrNonEq(LHS, RHS);

    public override BoolExpr ToExpr(NielsenGraph graph) {
        return graph.Ctx.MkEq(LHS.ToExpr(graph), RHS.ToExpr(graph));
    }

    public override int GetHashCode() {
        return 613461011 + LHS.GetHashCode() + 967118167 * RHS.GetHashCode();
    }

    public override string ToString() => $"{LHS} = {RHS}";
}