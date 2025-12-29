using Microsoft.Z3;
using System.Diagnostics;
using ZIPT.Constraints.ConstraintElement.AuxConstraints;
using ZIPT.Constraints.Modifier;
using ZIPT.IntUtils;
using ZIPT.MiscUtils;
using ZIPT.Strings.Chunks;
using ZIPT.Strings.Tokens;
using ZIPT.Strings.Tokens.RegexTokens;

namespace ZIPT.Constraints.ConstraintElement;

public sealed class StrMem : StrEqBase {

    public Str Str
    {
        get => LHS;
        private set => LHS = value;
    }

    public Str Regex
    {
        get => RHS;
        private set => RHS = value;
    }

    public uint Id { get; }

    public Str History { get; private set; }

    public override bool Sorted => false;

    public StrMem(Str str, Str regex, Str history, uint id) : base(str, regex) {
        Debug.Assert(LHS.RegexFree);
        // Debug.Assert(RHS.Ground);
        Id = id;
        History = history;
    }

    public override StrMem Apply(Subst subst, NielsenNode node) {
        var str = node.Env.StrManager.Subst(Str, subst);
        Debug.Assert(Regex.Ground);
        if (ReferenceEquals(str, Str))
            return this;
        return new StrMem(str, Regex, History, Id);
    }

    public override StrMem Apply(CharSubst subst, NielsenNode node) {
        var str  = node.Env.StrManager.Subst(node.Env, Str, subst);
        var regex = node.Env.StrManager.Subst(node.Env, Regex, subst);
        if (ReferenceEquals(str, Str) && ReferenceEquals(regex, Regex))
            return this;
        return new StrMem(str, regex, History, Id);
    }

    public override StrMem Apply(Interpretation itp) {
        var str = itp.Env.StrManager.Subst(Str, itp);
        var regex = itp.Env.StrManager.Subst(Regex, itp);
        if (ReferenceEquals(str, Str) && ReferenceEquals(regex, Regex))
            return this;
        return new StrMem(str, regex, History, Id);
    }

    public bool IsPrimitiveRegex() => 
        Str.Length == 1 && Str[0] is NamedStrToken;

    SimplifyResult SimplifyCharRegex(LocalInfo info, bool fwd) {
        var t = Str[fwd];
        Debug.Assert(Regex.Derivable);
        if (t is CharToken c) {
            Regex = Regex.Derivative(info.Env, c, fwd);
            if (fwd)
                History = info.Env.StrManager.Concat(History, c);
            Str = info.Env.StrManager.Drop(Str, fwd);
            return Regex.IsFail ? SimplifyResult.Conflict : SimplifyResult.Restart;
        }
        if (t is not SymCharToken sc)
            return SimplifyResult.Proceed;
        
        if (!info.CurrentNode.CharRanges.TryGetValue(sc, out CharacterSet? val))
            val = CharacterSet.Full;
        var min = Regex.FirstMinTerms();
        // TODO: maybe do it directly with the MinTerms structure?
        foreach (var s in min.ToCharacterSets()) {
            if (!val.IsSubset(s)) 
                continue;
            Regex = Regex.Derivative(info.Env, s, fwd);
            if (fwd)
                History = info.Env.StrManager.Concat(History, new SetToken(s));
            Str = info.Env.StrManager.Drop(Str, fwd);
            return Regex.IsFail ? SimplifyResult.Conflict : SimplifyResult.Restart;
        }
        // TODO: if all are disjoint we can even report a conflict
        return SimplifyResult.Proceed;
    }

    StarIntrModifier? ExtractCycle(LocalInfo info, NielsenEdge edge) {
        var mem = edge.Src.ConstraintsStrMem[Id];
        if (mem.History.Length == History.Length || Str.IsEmpty())
            // Nothing happened - we would pull out a \epsilon*
            return null;
        if (mem.History.Length >= History.Length ||
            !History.GetEnumerator().Take((int)mem.History.Length).SequenceEqual(mem.History.GetEnumerator()))
            return null;

        var first = Str.First;
        if (first is not NamedStrToken and not PowerToken)
            return null;
        Str b = info.Env.StrManager.DropLeft(History, mem.History.Length);
        if (b is { Length: 1, First: KleeneToken })
            return null;
        uint dropCnt;
        if (mem.History.Length > 0 && mem.History[mem.History.Length - 1] is KleeneToken k) {
            Debug.Assert(mem.History.Length == 1 || mem.History[mem.History.Length - 2] is not KleeneToken);
            dropCnt = b.Length + 1;
            //b = info.Env.StrManager.MkUnion([k.Base, b]);
            b = info.Env.StrManager.Concat(k, b);
        }
        else {
            dropCnt = b.Length;
        }

        Debug.Assert(!b.Nullable);
        //cases.Add(s);
        //Str cycleBase = info.Env.StrManager.MkUnion(cases);
        return new StarIntrModifier(Id, edge.Src, b, dropCnt);
    }

    SimplifyResult SimplifyDir(LocalInfo info, DetModifier sConstr, bool fwd) {
        while (Str.IsNonEmpty() && Regex.IsNonEmpty() && !IsPrimitiveRegex()) {
            
            var s = Str[fwd];
            var r = Regex[fwd];

            if (s is CharToken c1 && r is CharToken c2 && !c1.Equals(c2))
                return SimplifyResult.Conflict;

            var changed = SimplifyCharRegex(info, fwd);
            if (changed == SimplifyResult.Restart)
                continue;
            if (changed == SimplifyResult.Conflict)
                return SimplifyResult.Conflict;
            
            if (s is PowerToken p1) {
                if (info.CurrentNode.IsZero(p1.Power)) {
                    Str = info.Env.StrManager.Drop(Str, fwd);
                    continue;
                }
                if (!IsPrefixConsistent(info.CurrentNode, p1.Base, RHS, fwd)) {
                    sConstr.Add(new IntEq(info.CurrentNode.Env.ZeroInt, p1.Power));
                    return SimplifyResult.Proceed;
                }
            }

            if (SimplifyPowerSide(info, fwd))
                continue;
            break;
        }
        return SimplifyResult.Proceed;
    }

    protected override SimplifyResult SimplifyAndPropagateInternal(LocalInfo info, DetModifier sConstr, ref BacktrackReasons reason) {
        if (IsPrimitiveRegex()) {
            if (Str[0] is NamedStrToken v && Regex is { RegexFree: true, Ground: true }) {
                if (sConstr.Add(new Subst(v, Regex)))
                    return SimplifyResult.RestartAndSatisfied;
                return SimplifyResult.Restart;
            }
            return SimplifyResult.Proceed;
        }
        if (!Regex.Ground)
            // there could be a split variable on the RHS we need to get rid of first
            return SimplifyResult.Proceed;
        Log.WriteLine($"Simplify Membership : {Str} in {Regex}");
        if (SimplifyDir(info, sConstr, true) == SimplifyResult.Conflict) {
            reason = BacktrackReasons.SymbolClash;
            return SimplifyResult.Conflict;
        }

        if (SimplifyDir(info, sConstr, false) == SimplifyResult.Conflict) {
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

        if (Regex.IsFull)
            return SimplifyResult.Satisfied;

        if (Regex.IsEmpty()) {
            // Remove powers that actually do not exist anymore
            while (Str.IsNonEmpty() && Str[true] is PowerToken p) {
                Str? s;
                if ((s = SimplifyPowerSingle(info, p)) is not null) {
                    Str = info.Env.StrManager.DropLeft(Str);
                    Str = info.Env.StrManager.Concat(Str, s);
                    continue;
                }
                break;
            }
            if (Str.IsEmpty())
                return SimplifyResult.Satisfied;
            if (SimplifyEmpty(Str.GetEnumerator(), info.CurrentNode, sConstr) == SimplifyResult.Conflict) {
                reason = BacktrackReasons.SymbolClash;
                return SimplifyResult.Conflict;
            }
        }

        // check overapproximation for UNSAT
        if (!IsPrimitiveRegex() && !info.CurrentNode.CheckRegexWidending(Str, Regex)) {
            reason = BacktrackReasons.RegexWidening;
            return SimplifyResult.Conflict;
        }
        return SimplifyResult.Proceed;
    }

    static int extendCnt;

    public override ModifierBase? Extend(LocalInfo info, Dictionary<NamedInt, PDD<BigRational>> intSubst) {
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
        if (Str.First is PowerToken)
            return null;
        // Do this only at the very end - otw. we might loop as we introduce a Kleene star before reporting a conflict
        // Try loop generalisation
        if (info.RegexOccurrence.TryGetValue((Regex, Id), out int ex)) {
            var split = ExtractCycle(info, info.CurrentPath[ex]);
            if (split is not null)
                return split;
        }

        var first = Regex.FirstMinTerms();
        Debug.Assert(first.Intervals.Count > 0);

        if (Str.First is NamedStrToken v)
            return new RegexVarSplitModifier(v, first, true);
        return new RegexCharSplitModifier((SymCharToken)Str.First, first);

    }

    public override int CompareToInternal(StrConstraint other) {
        StrMem otherMem = (StrMem)other;
        int cmp = Id.CompareTo(otherMem.Id);
        if (cmp != 0)
            return cmp;
        cmp = LHS.Length.CompareTo(otherMem.LHS.Length);
        if (cmp != 0)
            return cmp;
        cmp = RHS.Length.CompareTo(otherMem.RHS.Length);
        if (cmp != 0)
            return cmp;
        cmp = History.Length.CompareTo(otherMem.History.Length);
        if (cmp != 0)
            return cmp;
        cmp = LHS.CompareTo(otherMem.LHS);
        if (cmp != 0)
            return cmp;
        cmp = RHS.CompareTo(otherMem.RHS);
        if (cmp != 0)
            return cmp;
        return History.CompareTo(otherMem.History);
    }

    public override StrConstraint Negate() => 
        new StrNonEq(LHS, RHS);

    public override BoolExpr ToExpr(Environment env, Dictionary<NamedStrToken, int> currentModificationCnt) => 
        (BoolExpr)env.ReMemFct.Apply(LHS.ToExpr(env, currentModificationCnt), RHS.ToExpr(env, currentModificationCnt));

    public override int GetHashCode() => 
        HashCode.Combine(LHS, RHS, History, Id) * 782620193;

    public override string ToString() => $"[{Id}] {LHS} in {RHS} : {History}";
}