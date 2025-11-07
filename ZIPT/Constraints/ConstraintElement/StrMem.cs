using Microsoft.Z3;
using System.Diagnostics;
using ZIPT.Constraints.ConstraintElement.AuxConstraints;
using ZIPT.Constraints.Modifier;
using ZIPT.IntUtils;
using ZIPT.MiscUtils;
using ZIPT.Strings.Chunks;
using ZIPT.Strings.Tokens;

namespace ZIPT.Constraints.ConstraintElement;

public sealed class StrMem : StrEqBase {

    public Str Str
    {
        get => LHS;
        set => LHS = value;
    }

    public Str Regex
    {
        get => RHS;
        set => RHS = value;
    }

    public override bool Sorted => false;

    public StrMem(Str str, Str regex) : base(str, regex) {
        Debug.Assert(LHS.RegexFree);
        // Debug.Assert(RHS.Ground);
    }

    public override StrMem Apply(Subst subst, NielsenNode node) {
        var str  = node.Env.StrManager.Subst(Str, subst);
        var regex = node.Env.StrManager.Subst(Regex, subst);
        if (ReferenceEquals(str, Str) && ReferenceEquals(regex, Regex))
            return this;
        return new StrMem(str, regex);
    }

    public override StrMem Apply(CharSubst subst, NielsenNode node) {
        var str  = node.Env.StrManager.Subst(node.Env, Str, subst);
        var regex = node.Env.StrManager.Subst(node.Env, Regex, subst);
        if (ReferenceEquals(str, Str) && ReferenceEquals(regex, Regex))
            return this;
        return new StrMem(str, regex);
    }

    public override StrMem Apply(Interpretation itp) {
        var str = itp.Env.StrManager.Subst(Str, itp);
        var regex = itp.Env.StrManager.Subst(Regex, itp);
        if (ReferenceEquals(str, Str) && ReferenceEquals(regex, Regex))
            return this;
        return new StrMem(str, regex);
    }

    public bool IsPrimitiveRegex() => 
        Str.Length == 1 && Str[0] is NamedStrToken;

    SimplifyResult SimplifyCharRegex(NielsenNode node, bool fwd) {
        var t = Str[fwd];
        Debug.Assert(Regex.Derivable);
        if (t is CharToken c) {
            Regex = Regex.Derivative(node.Env, c, fwd);
            Str = node.Env.StrManager.Drop(Str, fwd);
            return Regex.IsFail ? SimplifyResult.Conflict : SimplifyResult.Restart;
        }
        if (t is not SymCharToken sc)
            return SimplifyResult.Proceed;
        
        if (!node.CharRanges.TryGetValue(sc, out CharacterSet? val))
            val = CharacterSet.Full;
        var min = Regex.FirstMinTerms();
        // TODO: maybe do it directly with the MinTerms structure?
        foreach (var s in min.ToCharacterSets()) {
            if (!val.IsSubset(s)) 
                continue;
            Regex = Regex.Derivative(node.Env, s, fwd);
            Str = node.Env.StrManager.Drop(Str, fwd);
            return Regex.IsFail ? SimplifyResult.Conflict : SimplifyResult.Restart;
        }
        // TODO: if all are disjoint we can even report a conflict
        return SimplifyResult.Proceed;
    }

    SimplifyResult SimplifyDir(NielsenNode node, DetModifier sConstr, bool fwd) {
        while (Str.IsNonEmpty() && Regex.IsNonEmpty()) {
            if (SimplifySame(node.Env, fwd))
                continue;

            var s = Str[fwd];
            var r = Regex[fwd];

            if (s is CharToken c1 && r is CharToken c2 && !c1.Equals(c2))
                return SimplifyResult.Conflict;

            var changed = SimplifyCharRegex(node, fwd);
            if (changed == SimplifyResult.Restart)
                continue;
            if (changed == SimplifyResult.Conflict)
                return SimplifyResult.Conflict;
            
            if (s is PowerToken p1) {
                if (node.IsZero(p1.Power)) {
                    Str = node.Env.StrManager.Drop(Str, fwd);
                    continue;
                }
                if (!IsPrefixConsistent(node, p1.Base, RHS, fwd)) {
                    sConstr.Add(new IntEq(node.Env.ZeroInt, p1.Power));
                    return SimplifyResult.Proceed;
                }
            }

            if (SimplifyPowerSide(node, fwd))
                continue;
            break;
        }
        return SimplifyResult.Proceed;
    }

    protected override SimplifyResult SimplifyAndPropagateInternal(NielsenNode node, DetModifier sConstr, ref BacktrackReasons reason) {
        if (IsPrimitiveRegex()) {
            if (Str[0] is NamedStrToken v && Regex.RegexFree) {
                if (sConstr.Add(new Subst(v, Regex)) == SimplifyResult.Proceed)
                    return SimplifyResult.RestartAndSatisfied;
                return SimplifyResult.Restart;
            }
            return SimplifyResult.Proceed;
        }
        if (!Regex.Ground)
            // there could be a split variable on the RHS we need to get rid of first
            return SimplifyResult.Proceed;
        Log.WriteLine($"Simplify Membership : {Str} in {Regex}");
        if (SimplifyDir(node, sConstr, true) == SimplifyResult.Conflict) {
            reason = BacktrackReasons.SymbolClash;
            return SimplifyResult.Conflict;
        }

        if (SimplifyDir(node, sConstr, false) == SimplifyResult.Conflict) {
            reason = BacktrackReasons.SymbolClash;
            return SimplifyResult.Conflict;
        }

        if (Str.IsEmpty() && Regex.IsEmpty())
            return SimplifyResult.Satisfied;

        if (Str.IsEmpty()) {
            if (Regex.Nullable)
                return SimplifyResult.Satisfied;
            reason = BacktrackReasons.SymbolClash;
            return SimplifyResult.Conflict;
        }

        if (Regex.IsEmpty()) {
            // Remove powers that actually do not exist anymore
            while (Str.IsNonEmpty() && Str[true] is PowerToken p) {
                Str? s;
                if ((s = SimplifyPowerSingle(node, p)) is not null) {
                    Str = node.Env.StrManager.DropLeft(Str);
                    Str = node.Env.StrManager.Concat(Str, s);
                    continue;
                }
                break;
            }
            if (Str.IsEmpty())
                return SimplifyResult.Satisfied;
            if (SimplifyEmpty(Str.GetEnumerator(), node, sConstr) == SimplifyResult.Conflict) {
                reason = BacktrackReasons.SymbolClash;
                return SimplifyResult.Conflict;
            }
            return SimplifyResult.Proceed;
        }

        // check widening for UNSAT
        if (!IsPrimitiveRegex() && !node.CheckRegexWidending(Str, Regex)) {
            reason = BacktrackReasons.RegexWidening;
            return SimplifyResult.Conflict;
        }
        return SimplifyResult.Proceed;
    }

    ModifierBase? ExtendDir() {

        Debug.Assert(!LHS.IsEmpty() && !RHS.IsEmpty());
        return new DecomposeModifier(this);
    }

    static int extendCnt;

    public override ModifierBase? Extend(NielsenNode node, Dictionary<NamedInt, PDD<BigRational>> intSubst) {
        extendCnt++;
        // Don't sort -- this should have happened before in simplify!!
        if (IsPrimitiveRegex())
            return null;
        if (Regex.IsEmpty()) {
            Debug.Assert(!Str.IsEmpty());
            var t = Str[true];
            if (t is PowerToken p)
                return new PowerEpsilonModifier(p);
            // Simplify step should have already dealt with everything else!
            throw new NotSupportedException();
        }
        if (Str.First is not NamedStrToken or PowerToken)
            return null;
        return new DecomposeModifier(this);
    }

    public override int CompareToInternal(StrConstraint other) {
        StrEq otherEq = (StrEq)other;
        int cmp = LHS.Length.CompareTo(otherEq.LHS.Length);
        if (cmp != 0)
            return cmp;
        cmp = RHS.Length.CompareTo(otherEq.RHS.Length);
        if (cmp != 0)
            return cmp;
        cmp = LHS.CompareTo(otherEq.LHS);
        return cmp != 0 ? cmp : RHS.CompareTo(otherEq.RHS);
    }

    public override StrConstraint Negate() => 
        new StrNonEq(LHS, RHS);

    public override BoolExpr ToExpr(NielsenGraph graph) => 
        (BoolExpr)graph.Env.ReMemFct.Apply(LHS.ToExpr(graph), RHS.ToExpr(graph));

    public override int GetHashCode() => 
        HashCode.Combine(LHS.GetHashCode(), RHS.GetHashCode()) * 782620193;

    public override string ToString() => $"{LHS} in {RHS}";
}