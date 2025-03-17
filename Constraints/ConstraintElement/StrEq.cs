using System.Diagnostics;
using System.Security.Cryptography;
using System.Xml.Linq;
using System.Xml.XPath;
using Microsoft.Z3;
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

    // Given p^m and s=u_1 ... u_n
    // Counts the number of p in prefix of s
    static (Poly num, int idx) CommPower(NielsenNode node, Str @base, Str s) {
        // TODO: Check soundness
        Poly sum = new Poly();
        Len offset = 0;
        var pos = 0;
        var lastStableSum = sum;
        var lastStablePos = 0;
        int i = 0;
        for (; i < s.Count; i++) {
            if (pos == 0) {
                lastStablePos = i;
                lastStableSum = sum.Clone();
            }
            if (s[i].Equals(@base[pos])) {
                pos++;
                if (pos >= @base.Count) {
                    Debug.Assert(pos == @base.Count);
                    pos = 0;
                    offset += 1;
                }
                continue;
            }
            if (s[i] is PowerToken p2 && p2.Base.EqualsRotation(pos, @base)) {
                sum.AddPoly(p2.Power);
                continue;
            }
            break;
        }
        if (pos == 0) {
            lastStablePos = i;
            lastStableSum = sum;
        }
        lastStableSum.AddPoly(new Poly(offset));
        return (lastStableSum, lastStablePos);
    }

    static bool SimplifyEq(Str s1, Str s2, bool dir) {
        if (!s1.Peek(dir).Equals(s2.Peek(dir)))
            return false;
        Log.WriteLine("Simplify Eq: " + s1.Peek(dir) + "; " + s2.Peek(dir));
        s1.Drop(dir);
        s2.Drop(dir);
        return true;
    }

    static bool SimplifyPowerLrp(NielsenNode node, Str s, bool dir) {
        // Problem: It might unwind and compress the same term back and forth:
        // Assume n > 0 then  a^n => aa^{n-1} => a^n => ...
        return false;
        int i = 0;
        HashSet<Str> options = [];
        for (; i < s.Count; i++) {
            var t = s.Peek(dir, i);
            if (!t.Ground)
                break;
            if (t is PowerToken p)
                options.Add(p.Base);
        }
        foreach (var option in options) {
            var p = CommPower(node, option, s);
            if (p.idx <= 1)
                // either not found or just the element itself
                continue;
            for (int j = 0; j < p.idx; j++) s.Drop(dir);
            s.Add(new PowerToken(option, p.num), dir);
            return true;
        }
        return false;
    }

    static bool SimplifyPowerConst(NielsenNode node, Str s, PowerToken p, bool dir) {

        if (!dir)
            // TODO: Apply inverse
            return false;
        var bounds = p.Power.GetBounds(node);

        if (bounds.Max == 0) {
            Log.WriteLine("Simplify: Drop 0-power " + p);
            s.Drop(dir);
            return true;
        }
        if (p.Base.IsEmpty()) {
            Log.WriteLine("Simplify: Resolve empty-power " + p);
            s.Drop(dir);
            return true;
        }
        if (bounds.Max == 1) {
            Log.WriteLine("Simplify: Resolve 1-power " + p);
            s.Drop(dir);
            s.AddRange(p.Base, dir);
            return true;
        }
        if (p.Base.Peek(dir) is PowerToken p2)
            return SimplifyPowerConst(node, p.Base, p2, dir);
        return false;
    }

    bool SimplifyPowerElim(NielsenNode node, Str s1, Str s2, bool dir) {
        if (s1.Peek(dir) is not PowerToken p1)
            return false;
        // TODO: Query this from Z3's internal state
        if (SimplifyPowerLrp(node, s1, dir))
            return true;
        if (SimplifyPowerLrp(node, s2, dir))
            return true;
        if (SimplifyPowerConst(node, s1, p1, dir))
            return true;
        if (SimplifyPowerElim(node, p1, s1, s2, dir))
            return true;
        if (SimplifyPowerUnwind(node, p1, s1, dir))
            return true;
        if (s2.Peek(dir) is PowerToken p2) {
            if (SimplifyPowerConst(node, s2, p2, dir))
                return true;
            if (SimplifyPowerElim(node, p2, s2, s1, dir))
                return true;
            if (SimplifyPowerUnwind(node, p2, s2, dir))
                return true;
        }
        return false;
    }

    bool SimplifyPowerElim(NielsenNode node, PowerToken p, Str s1, Str s2, bool dir) {
        if (!dir)
            // TODO: Apply inverse
            return false;
        // TODO: As we already simplified it first, we can just check the front most tokens
        var r = CommPower(node, p.Base, s2);
        if (r.idx <= 0) 
            return false;
        r.num.SubPoly(p.Power);
        var b = r.num.GetBounds(node);
        if (b.Min <= 0) {
            // r.num <= p.Power
            s1.Drop(dir);
            for (var i = 0; i < r.idx; i++)
                s2.Drop(dir);
            s1.Add(new PowerToken(p.Base, r.num.Negate()), dir);
            Log.WriteLine("Simplify: power-elim " + p);
            return true;
        }
        if (b.Max >= 0) {
            // p.Power <= r.num
            s1.Drop(dir);
            for (var i = 0; i < r.idx; i++)
                s2.Drop(dir);
            s2.Add(new PowerToken(p.Base, r.num), dir);
            Log.WriteLine("Simplify: power-elim " + p);
            return true;
        }
        return false;
    }

    bool SimplifyPowerUnwind(NielsenNode node, PowerToken p, Str s, bool dir) {
        if (!dir)
            // TODO: Apply inverse
            return false;
        var bounds = p.Power.GetBounds(node);

        Debug.Assert(bounds.Max > 0); // Otw. it would be captured before

        if (bounds.Min <= 0) 
            return false;

        Log.WriteLine("Simplify: >0-unwinding power " + s.Peek(dir));
        s.Drop(dir);
        var sub = p.Power.Clone();
        sub.SubPoly(new Poly(1));
        s.Add(new PowerToken(p.Base, sub), dir);
        s.AddRange(p.Base, dir);
        return true;
    }

    SimplifyResult SimplifyDir(NielsenNode node, bool dir) {
        var s1 = LHS;
        var s2 = RHS;
        SortStr(ref s1, ref s2, dir);
        while (LHS.NonEmpty() && RHS.NonEmpty()) {
            SortStr(ref s1, ref s2, dir);
            Debug.Assert(s1.Count > 0);
            Debug.Assert(s2.Count > 0);

            if (SimplifyEq(s1, s2, dir))
                continue;

            if (s1.Peek(dir) is CharToken && s2.Peek(dir) is CharToken)
                return SimplifyResult.Conflict;

            if (SimplifyPowerElim(node, s1, s2, dir))
                continue;
            break;
        }
        return SimplifyResult.Proceed;
    }

    static SimplifyResult SimplifyEmpty(IEnumerable<StrToken> s, NielsenNode node, List<Subst> newSubst, HashSet<Constraint> newSideConstr) {
        foreach (var t in s) {
            if (t is CharToken)
                return SimplifyResult.Conflict;
            if (t is StrVarToken v)
                newSubst.Add(new Subst(v));
            else if (t is PowerToken p) {
                if (p.Power.GetBounds(node).Min > 0)
                    newSideConstr.Add(new StrEq(p.Base));
                else if (!p.Base.IsNullable(node))
                    newSideConstr.Add(new IntEq(p.Power));
            }
            else
                throw new NotSupportedException();
        }
        return SimplifyResult.Proceed;
    }

    // Try to add the substitution: x / s ==> do an occurrence check. If it fails, we have to add it as an ordinary equation
    public void AddDefinition(StrVarToken v, Str s, NielsenNode node, List<Subst> newSubst, HashSet<Constraint> newSideConstr) {
        if (s.RecursiveIn(v)) {
            newSideConstr.Add(new StrEq([v], s));
            return;
        }
        newSubst.Add(new Subst(v, s));
    }

    static int simplifyCount;

    protected override SimplifyResult SimplifyInternal(NielsenNode node, List<Subst> newSubst,
        HashSet<Constraint> newSideConstr) {
        simplifyCount++;
        Log.WriteLine("Simplify Eq (" + simplifyCount + "): " + LHS + " = " + RHS);
        if (SimplifyDir(node, true) == SimplifyResult.Conflict)
            return SimplifyResult.Conflict;
        if (SimplifyDir(node, false) == SimplifyResult.Conflict)
            return SimplifyResult.Conflict;

        if (LHS.IsEmpty() && RHS.IsEmpty())
            return SimplifyResult.Satisfied;

        if (LHS.IsEmpty() || RHS.IsEmpty()) {
            var eq = LHS.IsEmpty() ? RHS : LHS;
            // Remove powers that actually do not exist anymore
            while (eq.NonEmpty() && eq.Peek(true) is PowerToken p) {
                if (!SimplifyPowerConst(node, eq, p, true))
                    return SimplifyResult.Conflict;
            }
            if (eq.IsEmpty())
                return SimplifyResult.Satisfied;
            if (SimplifyEmpty(eq, node, newSubst, newSideConstr) == SimplifyResult.Conflict)
                return SimplifyResult.Conflict;
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
            if (SimplifyEmpty(nonEmpty.Keys, node, newSubst, newSideConstr) == SimplifyResult.Conflict)
                return SimplifyResult.Conflict;
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

    NumCmpModifier? SplitPowerElim(NielsenNode node, StrToken t, Str s) {
        if (t is not PowerToken p1)
            return null;
        var r = CommPower(node, p1.Base, s);
        return r.idx > 0 ? new NumCmpModifier(p1.Power, r.num) : null;
    }

    ModifierBase? SplitPowerIntr(StrToken t, Str s2) {
        if (t is not StrVarToken v)
            return null;

        var i = 0;
        bool simple = true;
        for (; i < s2.Count; i++) {
            if (s2[i] is CharToken)
                continue;
            if (s2[i].Equals(v))
                break;
            simple = false;
        }

        if (i >= s2.Count)
            return null;
        Debug.Assert(s2[i].Equals(v));

        if (simple) {
            // e.g., x... = aax... => (a)^n rather than (aa)^n || (aa)^n a [Optimization; not required]
            var s = new string(s2.Take(i).Select(o => ((CharToken)o).Value).ToArray());
            s = StringUtils.LeastRepeatedPrefix(s);
            // Just blast it; no overhead of symbolic postfix
            return new GPowerIntrModifier(v, 
                new Str(s.Select(o => (StrToken)new CharToken(o)).ToList()), false);
        }
        return new PowerIntrModifier(v,
            new Str(s2.Take(i).ToList()), false);
    }

    NumUnwindingModifier? SplitPowerUnwind(NielsenNode node, StrToken t) => 
        t is not PowerToken p ? null : new NumUnwindingModifier(p.Power);

    Str? TryGetPowerSplitBase(StrVarToken v, Str s, bool dir) {
        if (!dir || s.IsEmpty())
            return null;
        var i = 0;
        for (; i < s.Count && !s[i].Equals(v); i++) { }

        if (i >= s.Count)
            // Non-rec Case
            return null;
        // Rec Case
        Debug.Assert(s[i].Equals(v));
        return new Str(s.Take(i).ToList());
    }

    ModifierBase? SplitVarVar(NielsenNode node, Str s1, Str s2) {
        if (s1.IsEmpty() || s2.IsEmpty() || s1[0] is not StrVarToken v1 || s2[0] is not StrVarToken v2)
            return null;

        Str? p1 = TryGetPowerSplitBase(v1, s2, true);
        Str? p2 = TryGetPowerSplitBase(v2, s1, true);
        if (p1 is not null && p2 is not null) {
            if (p1.Ground && p2.Ground)
                return new GPowerGPowerIntrModifier(v1, v2, p1, p2, false);
            if (p1.Ground)
                return new CombinedModifier(
                    new GPowerIntrModifier(v1, p1, false),
                    new ConstNielsenModifier(v2, v1, false)
                );
            //return new GPowerPowerIntrModifier(v1, v2, p1, p2, false);
            if (p2.Ground)
                return new CombinedModifier(
                    new GPowerIntrModifier(v2, p2, false),
                    new ConstNielsenModifier(v1, v2, false)
                );
                // return new GPowerPowerIntrModifier(v2, v1, p2, p1, false);
            return
                new VarNielsenModifier(v1, v2, false);
            //return new PowerPowerIntrModifier(v1, v2, p1, p2, false);
        }
        if (p1 is not null) {
            (p1, p2) = (p2, p1);
            (v1, v2) = (v2, v1);
            (s1, s2) = (s2, s1);
        }
        if (p1 is null)
            return new VarNielsenModifier(v1, v2, false);
        if (p1.Ground)
            return new GPowerIntrConstNielsen(v1, v2, p1, false);
        return new PowerIntrConstNielsen(v1, v2, p1, false);
    }

    ModifierBase? SplitVarChar(NielsenNode node, StrToken t, Str s) {
        if (t is not StrVarToken v || s.IsEmpty() || s[0] is not CharToken)
            return null;
        Str? p = TryGetPowerSplitBase(v, s, true);
        if (p is null)
            return new ConstNielsenModifier(v, s.Peek(true), false);
        if (p.Ground)
            return new GPowerIntrModifier(v, p, false);
        return new PowerIntrModifier(v, p, false);
    }

    ModifierBase? SplitVarPower(NielsenNode node, StrToken t1, StrToken t2) {
        if (t1 is not StrVarToken v || t2 is not PowerToken p || !p.Ground)
            return null;
        throw new NotImplementedException();
        return null;
    }

    public override ModifierBase Extend(NielsenNode node) {
        Str s1 = LHS;
        Str s2 = RHS;
        SortStr(ref s1, ref s2, true);
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

        var t1 = s1.Peek(true);
        var t2 = s2.Peek(true);

        ModifierBase? ret;

        if ((ret = SplitPowerElim(node, t1, s2)) is not null)
            return ret;
        if ((ret = SplitPowerElim(node, t2, s1)) is not null)
            return ret;
        // if ((ret = SplitPowerIntr(t1, s2)) is not null)
        //     return ret;
        // if ((ret = SplitPowerIntr(t2, s1)) is not null)
        //     return ret;
        if (t2 is not StrVarToken && (ret = SplitPowerUnwind(node, t1)) is not null)
            return ret;
        if (t2 is not StrVarToken && (ret = SplitPowerUnwind(node, t2)) is not null)
            return ret;
        if ((ret = SplitVarVar(node, s1, s2)) is not null)
            return ret;
        if ((ret = SplitVarChar(node, t1, s2)) is not null)
            return ret;
        if ((ret = SplitVarChar(node, t2, s1)) is not null)
            return ret;
        if ((ret = SplitVarPower(node, t1, t2)) is not null)
            return ret;
        if ((ret = SplitVarPower(node, t2, t1)) is not null)
            return ret;
        if ((ret = SplitPowerUnwind(node, t1)) is not null)
            return ret;
        if ((ret = SplitPowerUnwind(node, t2)) is not null)
            return ret;
        throw new NotSupportedException();
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

    public override string ToString() {
        return $"{LHS} = {RHS}";
    }

}