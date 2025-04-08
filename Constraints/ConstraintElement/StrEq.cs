using System.Diagnostics;
using System.Diagnostics.CodeAnalysis;
using Microsoft.Z3;
using StringBreaker.Constraints.ConstraintElement.AuxConstraints;
using StringBreaker.Constraints.Modifier;
using StringBreaker.IntUtils;
using StringBreaker.MiscUtils;
using StringBreaker.Strings;
using StringBreaker.Strings.Tokens;

namespace StringBreaker.Constraints.ConstraintElement;

public sealed class StrEq : StrEqBase {

    public StrEq(NielsenContext ctx, StrRef lhs, StrRef rhs) : base(ctx, lhs, rhs) { }
    public StrEq(NielsenContext ctx, StrRef empty) : base(ctx, new StrRef([]), empty) { }

    public override StrEq Clone(NielsenContext ctx) => 
        new(ctx, LHS.Clone(), RHS.Clone());

    static SimplifyResult SimplifyEmpty(NielsenContext ctx, StrRef s, 
        List<Subst> newSubst, HashSet<Constraint> newSideConstr) {

        StrTokenRef? t;
        while ((t = s.PeekFirst(ctx)) is not null) {
            if (t.Token is UnitToken)
                return SimplifyResult.Conflict;
            if (t.Token is StrVarToken)
                newSubst.Add(new SubstVar(t));
            else if (t.Token is PowerToken p) {
                if (ctx.IsLt(new Poly(), p.Power))
                    // p.Power > 0
                    newSideConstr.Add(new StrEq(ctx, p.Base));
                else if (!p.Base.IsNullable(ctx))
                    // p.Base != ""
                    newSideConstr.Add(new IntEq(p.Power));
            }
            else
                throw new NotSupportedException();
        }
        return SimplifyResult.Proceed;
    }

    // Try to add the substitution: x / s ==> do an occurrence check. If it fails, we have to add it as an ordinary equation
    public void AddDefinition(StrTokenRef v, StrRef s, NielsenContext ctx, List<Subst> newSubst, HashSet<Constraint> newSideConstr) {
        Debug.Assert(v.Token is NamedStrToken);
        if (s.RecursiveIn(v))
            // newSideConstr.Add(new StrEq([v], s));
            return;
        newSubst.Add(new SubstVar(v, s));
    }

    SimplifyResult SimplifyDir(NielsenContext ctx, List<Subst> newSubst, HashSet<Constraint> newSideConstr, bool dir) {
        // This can cause problems, as it might unwind/compress the beginning/end over and over again (might even detect it as subsumed)
        var s1 = LHS;
        var s2 = RHS;
        SortStr(ctx, ref s1, ref s2, dir);
        while (!LHS.IsEpsilon(ctx) && !RHS.IsEpsilon(ctx)) {

            SortStr(ctx, ref s1, ref s2, dir);
            if (SimplifySame(ctx, s1, s2, dir))
                continue;

            var t1 = s1.Peek2(ctx, dir);
            var t2 = s2.Peek2(ctx, dir);

            if (t1.Token is UnitToken u1 && t2.Token is UnitToken u2 && ctx.AreDiseq(u1, u2))
                return SimplifyResult.Conflict;

            if (t1.Token is SymCharToken sc1) {
                if (t2.Token is UnitToken u) {
                    newSubst.Add(new SubstSChar(sc1, u));
                    return SimplifyResult.Proceed;
                }
            }

            if (t1.Token is PowerToken p1) {
                if (ctx.IsZero(p1.Power)) {
                    s1.Skip(ctx, dir);
                    continue;
                }
                if (!IsPrefixConsistent(ctx, p1.Base, s2, dir)) {
                    newSideConstr.Add(new IntEq(new Poly(), p1.Power));
                    return SimplifyResult.Proceed;
                }
            }
            if (t2.Token is PowerToken p2) {
                if (ctx.IsZero(p2.Power)) {
                    s2.Skip(ctx, dir);
                    continue;
                }
                if (!IsPrefixConsistent(ctx, p2.Base, s1, dir)) {
                    newSideConstr.Add(new IntEq(new Poly(), p2.Power));
                    return SimplifyResult.Proceed;
                }
            }

            if (t2.Token is NamedStrToken) {
                (s1, s2) = (s2, s1);
                (t1, t2) = (t2, t1);
            }
            if (t1.Token is NamedStrToken && t2.Token is CharToken && s1.Peek(ctx, 1, dir)?.Token is CharToken) {
                Debug.Assert(!s2.IsEpsilon(ctx));
                // uxw = xvw', u & v char only
                // x / u' x with u' <= u while u' incompatible with v
                // we do not want to unwind stuff like axx = xbx - this would result in an infinite sequence (the power would eliminate it anyway!)
                // e.g., xababc w = abc w' sets x / abcx as "ababc" is incompatible with "abc",
                //       xabca w = abc w' would not reduce at all, and
                //       xaabca w = abc w' would set x / ax
                StrRef it = s2.Clone();
                int cnt = 0;
                while (it.Peek(ctx, dir)?.Token is CharToken) {

                    // TODO: Use consistent prefix (requires some resource improvements first though)
                    StrRef it1 = s1.Clone();
                    var r = it1.Skip(ctx, dir);
                    StrRef it2 = s2.Clone();
                    Debug.Assert(r is not null);
                    bool failed = false;
                    while (true) {
                        StrTokenRef? st1 = it1.Peek(ctx, dir);
                        if (st1 is null)
                            break;
                        it1.Skip(ctx, dir);
                        StrTokenRef? st2 = it2.Peek(ctx, dir);
                        if (st2 is null)
                            break;
                        it2.Skip(ctx, dir);
                        if (st1.Token is not CharToken stc1 || st2.Token is not CharToken stc2)
                            break;
                        if (!stc1.Equals(stc2)) {
                            failed = true;
                            break;
                        }
                    }
                    if (!failed) 
                        break;
                    // The prefix are inconsistent - we can proceed
                    cnt++;
                }
                if (cnt > 0) {
                    // Check if the next variable is not the variable we started of (unwinding this way would not necessarily terminate)
                    // => Use power instead
                    StrRef it3 = it.Clone();
                    while (it3.Peek(ctx, dir)?.Token is UnitToken) {
                        it3.Skip(ctx, dir);
                    }
                    if (it3.IsEpsilon(ctx) || !t1.Equals(it3.Peek(ctx, dir)!)) {
                        // t == v1 => we need power introduction 
                        var cit = s2.Clone();
                        Str s = new(ctx, cit, it, [t1], dir, cnt + 1);
                        Debug.Assert(cit.Equals(it));
                        newSubst.Add(new SubstVar(t1, s));
                        return SimplifyResult.Proceed;
                    }
                }
            }

            if (SimplifyPower(ctx, s1, s2, dir))
                continue;
            break;
        }
        return SimplifyResult.Proceed;
    }

    static int simplifyCount;

    protected override SimplifyResult SimplifyInternal(NielsenContext ctx, 
        List<Subst> newSubst, HashSet<Constraint> newSideConstr, 
        ref BacktrackReasons reason) {
        simplifyCount++;
        Log.WriteLine($"Simplify Eq ({simplifyCount}): {LHS} = {RHS}");
        LHS = LcpCompression(LHS) ?? LHS;
        RHS = LcpCompression(RHS) ?? RHS;
        if (SimplifyDir(ctx, newSubst, newSideConstr, true) == SimplifyResult.Conflict) {
            reason = BacktrackReasons.SymbolClash;
            return SimplifyResult.Conflict;
        }
        if (newSubst.IsNonEmpty())
            return SimplifyResult.Proceed;

        if (SimplifyDir(ctx, newSubst, newSideConstr, false) == SimplifyResult.Conflict) {
            reason = BacktrackReasons.SymbolClash;
            return SimplifyResult.Conflict;
        }
        if (newSubst.IsNonEmpty())
            return SimplifyResult.Proceed;

        bool e1 = LHS.IsEpsilon(ctx);
        bool e2 = RHS.IsEpsilon(ctx);

        if (e1 && e2)
            return SimplifyResult.Satisfied;

        if (e1 || e2) {
            var eq = e1 ? RHS : LHS;
            // Remove powers that actually do not exist anymore
            while (eq.Peek(ctx, true)?.Token is PowerToken p) {
                StrRef? s;
                if ((s = SimplifyPowerSingle(ctx, p)) is not null) {
                    eq.Skip(ctx, true);
                    eq.AddRange(s, true);
                    continue;
                }
                break;
            }
            if (eq.IsEpsilon(ctx))
                return SimplifyResult.Satisfied;
            if (SimplifyEmpty(ctx, eq, newSubst, newSideConstr) == SimplifyResult.Conflict) {
                reason = BacktrackReasons.SymbolClash;
                return SimplifyResult.Conflict;
            }
            SortStr(ctx);
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
                StrRef? s;
                if ((s = SimplifyPowerSingle(ctx, p)) is not null) {
                    nonEmpty.RemoveAll(p);
                    nonEmpty.Add(s);
                    continue;
                }
                break;
            }
            if (SimplifyEmpty(ctx, nonEmpty.Keys, newSubst, newSideConstr) == SimplifyResult.Conflict) {
                reason = BacktrackReasons.ParikhImage;
                return SimplifyResult.Conflict;
            }
            SortStr(ctx);
            return SimplifyResult.Proceed;
        }

        // Propagate assignments
        StrTokenRef? t1, t2 = null;
        if ((LHS.IsUnit(ctx, out t1) && t1?.Token is StrVarToken) ||
            (RHS.IsUnit(ctx, out t2) && t2?.Token is StrVarToken)) {
            var (v, s) = t2 is not null ? (t2, LHS) : (t1, RHS);
            AddDefinition(v!, s, ctx, newSubst, newSideConstr);
        }
        SortStr(ctx);
        return SimplifyResult.Proceed;
    }

    NumCmpModifier? SplitPowerElim(NielsenContext ctx, StrTokenRef t, StrRef s, bool dir) {
        if (t.Token is not PowerToken p1)
            return null;
        var r = CommPower(p1.Base, s, dir);
        return r.idx > 0 ? new NumCmpModifier(p1.Power, r.num) : null;
    }

    NumUnwindingModifier? SplitPowerUnwind(NielsenContext ctx, StrTokenRef t, bool varInvolved) => 
        t.Token is not PowerToken p ? null : (varInvolved ? new VarNumUnwindingModifier(p.Power) : new ConstNumUnwindingModifier(p.Power));

    StrRef? TryGetPowerSplitBase(NielsenContext ctx, StrVarToken v, StrRef s, bool dir) {
        if (s.IsEpsilon(ctx))
            return null;
        var i = 0;
        for (; i < s.Count && !s.Peek(dir, i).Equals(v); i++) { }

        if (i >= s.Count)
            // Non-rec Case
            return null;
        // Rec Case
        Debug.Assert(s.Peek(dir, i).Equals(v));
        return dir 
            ? new StrRef(s.Take(i).ToList()) 
            : new StrRef(s.Reverse().Take(i).Reverse().ToList());
    }

    ModifierBase? SplitEq(NielsenContext ctx, StrRef s1, StrRef s2, bool dir) {
        if (s1.IsEpsilon(ctx) || s2.IsEpsilon(ctx))
            return null;
        // TODO: This is not optimal!
        Len constDiff = 0;
        Len best = Len.PosInf;
        int bestLhs = 0, bestRhs = 0;
        Poly lhs = new(), rhs = new();
        int lhsIdx = 0; int rhsIdx = 0;
        // We are only interested for padding in the first time the variables are equal (but we are looking for that case for a minimal constant difference as well)
        bool firstTimeEqVars = true;
        while (lhsIdx < s1.Count || rhsIdx < s2.Count) {
            if (lhsIdx > 0 || rhsIdx > 0) {
                // TODO
                // Set best only if this is the first time the difference is empty
                // But continue to find potential 0-splits
                if (lhs.IsZero && rhs.IsZero) {
                    if (firstTimeEqVars && constDiff.Abs() < best) {
                        best = constDiff;
                        bestLhs = lhsIdx;
                        bestRhs = rhsIdx;
                    }
                    if (constDiff.IsZero)
                        return new EqSplitModifier(this, lhsIdx, rhsIdx, dir);
                }
            }
            Poly len;
            if (lhs.IsEmpty() && rhs.IsNonEmpty() ||
                (lhs.IsEmpty() && rhs.IsEmpty() && constDiff.IsNeg)) {

                if (s1.Count <= lhsIdx)
                    break;
                len = LenVar.MkLenPoly([s1.Peek2(ctx, dir, lhsIdx++)]);
                constDiff += len.ConstPart;
                len.ElimConst();
                firstTimeEqVars &= best.IsInf || len.IsZero /* there is no variable */;
                if (!len.IsZero) {
                    lhs.Plus(len);
                    Poly.ElimCommon(lhs, rhs);
                }
                continue;
            }
            if (s2.Count <= rhsIdx)
                break;
            len = LenVar.MkLenPoly([s2.Peek2(ctx, dir, rhsIdx++)]);
            constDiff -= len.ConstPart;
            len.ElimConst();
            firstTimeEqVars &= best.IsInf || len.IsZero /* there is no variable */;
            if (!len.IsZero) {
                rhs.Plus(len);
                Poly.ElimCommon(lhs, rhs);
            }
        }
        if (best.IsInf)
            return null;
        Debug.Assert(!best.IsZero);
        int val;
        if (best.IsNeg) {
            if (bestLhs >= 0 && s1.Peek(ctx, dir, bestLhs)?.Token is StrVarToken v11 && best.TryGetInt(out val))
                // ...|x... (=> x / o_1...o_p x)
                return new VarPaddingModifier(v11, -val, dir);
            if (bestRhs > 0 && bestRhs <= s2.Count && s2.Peek(ctx, dir, bestRhs - 1) is StrVarToken v22 && best.TryGetInt(out val))
                // ...x|... (=> x / x o_1...o_p x)
                return new VarPaddingModifier(v22, -val, !dir);
            return null;
        }
        if (bestRhs >= 0 && s2.Peek(ctx, dir, bestRhs)?.Token is StrVarToken v21 && best.TryGetInt(out val))
            return new VarPaddingModifier(v21, val, dir);
        if (bestLhs > 0 && bestLhs <= s1.Count && s1.Peek(ctx, dir, bestLhs - 1) is StrVarToken v12 && best.TryGetInt(out val))
            return new VarPaddingModifier(v12, val, !dir);
        return null;
    }

    ModifierBase? SplitVarVar(NielsenContext ctx, StrRef s1, StrRef s2, bool dir) {
        if (s1.Peek(ctx, dir)?.Token is not StrVarToken v1 || s2.Peek(ctx, dir)?.Token is not StrVarToken v2)
            return null;

        StrRef? p1 = TryGetPowerSplitBase(ctx, v1, s2, dir);
        StrRef? p2 = TryGetPowerSplitBase(ctx, v2, s1, dir);
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

    ModifierBase? SplitGroundPower(NielsenContext ctx, StrToken t, StrRef s, bool dir) {
        if (t is not StrVarToken v || s.Peek(ctx, dir)?.Token is not UnitToken)
            return null;
        StrRef? p = TryGetPowerSplitBase(ctx, v, s, dir);
        if (p is not null && p.Ground)
            return new GPowerIntrModifier(v, p, dir);
        return null;
    }

    ModifierBase? SplitVarChar(NielsenContext ctx, StrToken t, StrRef s, bool dir) {
        if (t is not StrVarToken v || s.Peek(ctx, dir)?.Token is not UnitToken)
            return null;
        StrRef? p = TryGetPowerSplitBase(ctx, v, s, dir);
        if (p is null)
            return new ConstNielsenModifier(v, s.Peek(dir), dir);
        if (p.Ground) {
            Debug.Assert(false); // This should be excluded before (SplitGroundPower)
            return new GPowerIntrModifier(v, p, dir);
        }
        return new ConstNielsenModifier(v, s.Peek(dir), dir);
        //return new PowerIntrModifier(v, p, dir);
    }

    ModifierBase? SplitVarPower(NielsenContext ctx, StrToken t, StrRef s, bool dir) {
        if (t is not StrVarToken v || s.Peek(ctx, dir)?.Token is not PowerToken { Ground: true } p)
            return null;

        StrRef? b = TryGetPowerSplitBase(ctx, v, s, dir);
        if (b is null)
            return new PowerSplitModifier(v, p, dir);
        if (b.Ground)
            return new GPowerIntrModifier(v, b, dir);
        return new PowerSplitModifier(v, p, dir);
    }

    ModifierBase ExtendDir(NielsenContext ctx, bool dir) {
        StrRef s1 = LHS;
        StrRef s2 = RHS;
        StrEqBase.SortStr(ctx, ref s1, ref s2, dir);
        if (s1.IsEpsilon(ctx)) {
            Debug.Assert(!s2.IsEpsilon(ctx));
            foreach (var s in s2) {
                if (s is PowerToken p)
                    return new PowerEpsilonModifier(p);
                // Simplify step should have already dealt with everything else!
                throw new NotSupportedException();
            }
            throw new NotSupportedException();
        }
        Debug.Assert(!s1.IsEpsilon(ctx) && !s2.IsEpsilon(ctx));

        var t1 = s1.Peek2(ctx,dir);
        var t2 = s2.Peek2(ctx, dir);

        ModifierBase? ret;

        if ((ret = SplitPowerElim(ctx, t1, s2, dir)) is not null)
            return ret;
        if ((ret = SplitPowerElim(ctx, t2, s1, dir)) is not null)
            return ret;
        if (t2.Token is not NamedStrToken && (ret = SplitPowerUnwind(ctx, t1, false)) is not null)
            return ret;
        if (t1.Token is not NamedStrToken && (ret = SplitPowerUnwind(ctx, t2, false)) is not null)
            return ret;
        if ((ret = SplitGroundPower(ctx, t1, s2, dir)) is not null)
            return ret;
        if ((ret = SplitGroundPower(ctx, t2, s1, dir)) is not null)
            return ret;
        if ((ret = SplitEq(ctx, s1, s2, dir)) is not null)
            return ret;
        if ((ret = SplitVarPower(ctx, t1, s2, dir)) is not null)
            return ret;
        if ((ret = SplitVarPower(ctx, t2, s1, dir)) is not null)
            return ret;
        if ((ret = SplitVarChar(ctx, t1, s2, dir)) is not null)
            return ret;
        if ((ret = SplitVarChar(ctx, t2, s1, dir)) is not null)
            return ret;
        if ((ret = SplitVarVar(ctx, s1, s2, dir)) is not null)
            return ret;
        if ((ret = SplitPowerUnwind(ctx, t1, true)) is not null)
            return ret;
        if ((ret = SplitPowerUnwind(ctx, t2, true)) is not null)
            return ret;
        throw new NotSupportedException();
    }

    public override ModifierBase Extend(NielsenContext ctx) {
        var m1 = ExtendDir(ctx, true);
        var m2 = ExtendDir(ctx, false);
        return m1.CompareTo(m2) <= 0 ? m1 : m2;
    }

    public override int CompareToInternal(StrConstraint other) {
        StrEq otherEq = (StrEq)other;
        int cmp = LHS.CompareTo(otherEq.LHS);
        return cmp != 0 ? cmp : RHS.CompareTo(otherEq.RHS);
    }

    public override StrConstraint Negate(NielsenContext ctx) => 
        new StrNonEq(ctx, LHS, RHS);

    public override BoolExpr ToExpr(NielsenContext ctx) {
        return ctx.Graph.Ctx.MkEq(LHS.ToExpr(ctx), RHS.ToExpr(ctx));
    }

    public override string ToString() => $"{LHS} = {RHS}";
}