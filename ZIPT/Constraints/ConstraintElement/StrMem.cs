using Microsoft.Z3;
using System.Diagnostics;
using System.Runtime.InteropServices;
using ZIPT.Constraints.Modifier;
using ZIPT.IntUtils;
using ZIPT.MiscUtils;
using ZIPT.Strings.Chunks;
using ZIPT.Strings.Tokens;
using ZIPT.Strings.Tokens.RegexTokens;
using static System.Runtime.InteropServices.JavaScript.JSType;

namespace ZIPT.Constraints.ConstraintElement;

// Annotated regex membership constraint <C, Str, Regex, History> asserting Str \in L(Regex).
// History records the consumed prefixes and is used for cycle detection and stabilizer extraction.
public sealed class StrMem : StrEqBase {

    // The string term that must belong to L(Regex).
    public Str Str
    {
        get => LHS;
        private set => LHS = value;
    }

    // The regular expression defining the accepted language.
    public Str Regex
    {
        get => RHS;
        private set => RHS = value;
    }

    // Stable identifier for this constraint; key in ConstraintsStrMem and used for cycle tracking via RegexOccurrence.
    public uint Id { get; }

    // Sequence of characters/minterms consumed from Str so far; extended by SimplifyCharRegex and reset on cycle detection.
    public Str History { get; private set; }

    public override bool Sorted => false;

    // Create a new membership constraint with given id and history.
    public StrMem(Str str, Str regex, Str history, uint id, DependencyTracker reason) : base(str, regex, reason) {
        Debug.Assert(LHS.RegexFree);
        // Debug.Assert(RHS.Ground);
        Id = id;
        History = history;
    }

    // Apply a substitution to this constraint and return a new instance if changed.
    public override StrMem Apply(Subst subst, NielsenNode node) {
        var str = node.Env.StrManager.Subst(Str, subst);
        Debug.Assert(Regex.Ground);
        if (ReferenceEquals(str, Str))
            return this;
        return new StrMem(str, Regex, History, Id, Reason.Merge(subst.Reason));
    }

    // Apply a character-level substitution to both sides and return updated constraint if any change.
    public override StrMem Apply(CharSubst subst, NielsenNode node) {
        var str  = node.Env.StrManager.Subst(node.Env, Str, subst);
        var regex = node.Env.StrManager.Subst(node.Env, Regex, subst);
        if (ReferenceEquals(str, Str) && ReferenceEquals(regex, Regex))
            return this;
        return new StrMem(str, regex, History, Id, Reason.Merge(subst.Reason));
    }

    // Apply an interpretation (evaluation of variables) to produce a concrete constraint.
    public override StrMem Apply(Interpretation itp) {
        var str = itp.Env.StrManager.Subst(Str, itp);
        var regex = itp.Env.StrManager.Subst(Regex, itp);
        if (ReferenceEquals(str, Str) && ReferenceEquals(regex, Regex))
            return this;
        return new StrMem(str, regex, History, Id, Reason);
    }

    // A constraint is primitive when Str is a single variable; at that point it directly constrains that variable's language.
    public bool IsPrimitiveRegex() => 
        Str.Length == 1 && Str[0] is NamedStrToken;

    // Consumes one leading (or trailing, if !fwd) token by taking a Brzozowski derivative.
    // Returns Restart on progress, Conflict if the resulting regex is empty, Proceed if the token is not yet concrete.
    SimplifyResult SimplifyCharRegex(LocalInfo info, bool fwd) {
        var t = Str[fwd];
        Debug.Assert(Regex.Derivable);
        if (t is CharToken c) {
            var prevRegex = Regex;
            Regex = Regex.Derivative(info.Env, c, fwd);
            if (fwd) {
                // Propagate self-stabilizing flag: states reachable from a self-stabilizing regex need no further stabilizer analysis.
                if (info.Env.IsSelfStabilizing(prevRegex) && !Regex.IsFail)
                    info.Env.SetSelfStabilizing(Regex);
                History = info.Env.StrManager.Concat(History, c);
            }
            Str = info.Env.StrManager.Drop(Str, fwd);
            return Regex.IsFail ? SimplifyResult.Conflict : SimplifyResult.Restart;
        }
        if (t is not SymCharToken sc)
            return SimplifyResult.Proceed;

        if (!info.CurrentNode.CharRanges.TryGetValue(sc, out CharacterSet? val))
            val = CharacterSet.Full;
        var min = Regex.FirstMinTerms();
        // Try to match symbolic character token against regex first minterms.
        // If a minterm fully contains the current symbolic set, take its derivative.
        foreach (var s in min.ToCharacterSets()) {
            // sc must be fully contained in the minterm s to take this branch of the derivative.
            if (!val.IsSubset(s)) 
                continue;
            var prevRegex = Regex;
            Regex = Regex.Derivative(info.Env, s, fwd);
            if (fwd) {
                if (info.Env.IsSelfStabilizing(prevRegex) && !Regex.IsFail)
                    info.Env.SetSelfStabilizing(Regex);
                History = info.Env.StrManager.Concat(History, new SetToken(s));
            }
            Str = info.Env.StrManager.Drop(Str, fwd);
            return Regex.IsFail ? SimplifyResult.Conflict : SimplifyResult.Restart;
        }
        // TODO: if all are disjoint we can even report a conflict
        return SimplifyResult.Proceed;
    }

    // Extract a blocking stabilizer from a detected cycle in search
    StarIntrModifier? ExtractCycle(LocalInfo info, NielsenEdge edge) {
        var mem = edge.Src.ConstraintsStrMem[Id];
        // If history did not advance or string empty, no non-trivial cycle to extract.
        if (mem.History.Length == History.Length || Str.IsEmpty())
            // Nothing happened - we would pull out a \epsilon
            return null;
        if (mem.History.Length >= History.Length ||
            !History.GetEnumerator().Take((int)mem.History.Length).SequenceEqual(mem.History.GetEnumerator()))
            return null;

        var first = Str.First;
        if (first is not NamedStrToken and not PowerToken)
            return null;
        Str rawCycle = info.Env.StrManager.DropLeft(History, mem.History.Length);
        if (rawCycle is { Length: 1, First: KleeneToken })
            return null;
        uint dropCnt;
        if (mem.History.Length > 0 && mem.History[mem.History.Length - 1] is KleeneToken k) {
            Debug.Assert(mem.History.Length == 1 || mem.History[mem.History.Length - 2] is not KleeneToken);
            dropCnt = rawCycle.Length + 1;
        }
        else
            dropCnt = rawCycle.Length;

        if (!info.Env.IsSelfStabilizing(Regex)) {
            // Build strengthened stabilizer using the history tokens and intermediate stabilizers
            Str strengthened = StabilizerFromCycle(info.Env, Regex, rawCycle);
            if (strengthened.IsEmpty() || strengthened.Nullable)
                return null;

            // Add stabilizer to the set of known stabilizers
            info.Env.AddStabilizer(Regex, info.Env.StrManager.MkStar(strengthened));
        }

        // Use the full union of all known stabilizers for decomposition
        Str stabUnion = info.Env.GetStabilizerUnion(Regex);
        return new StarIntrModifier(Id, edge.Src, stabUnion, dropCnt, Reason);
    }

    // Compute strengthened stabilizer from cycle
    static Str StabilizerFromCycle(Environment env, Str regex, Str cycleHistory) {
        // Extract character tokens from the cycle history 
        EList<(StrToken token, CharacterSet charSet)> currentCycle = [];
        HashSet<EList<(StrToken token, CharacterSet charSet)>> cycles = [];
        Str s = regex;
        foreach (var t in cycleHistory.GetEnumerator()) {
            CharacterSet cs;
            if (t is CharToken ct)
                cs = new CharacterSet(new CharacterRange(ct.Value));
            else if (t is SetToken st)
                cs = st.Set;
            else {
                Debug.Assert(false);
                continue;
            }
            currentCycle.Add((t, cs));
            s = s.Derivative(env, cs, true);
            if (ReferenceEquals(s, regex)) {
                // We found a shorter cycle
                // This can in fact happen in case we substituted a larger chunk before
                // e.g., x... \in .* and we apply x / ab
                // we would get both a "a" and a "b" cycle.
                cycles.Add(currentCycle);
                currentCycle = [];
            }
        }

        if (currentCycle.Count > 0)
            cycles.Add(currentCycle);

        if (cycles.Count == 0)
            return env.EmptyStr;

        Debug.Assert(cycles.All(o => o.Count > 0));
        List<Str> cases = [];

        foreach (var chars in cycles) {
            // Build stabilizer iteratively: include filtered stabilizers between tokens
            Str result = env.EmptyStr;
            Str currentRegex = regex;

            for (int i = 0; i < chars.Count; i++) {
                var (token, charSet) = chars[i];

                if (i > 0) {
                    // Insert sub-stabilizer that cannot start with characters in charSet
                    Str stabPart = GetFilteredStabilizerStar(env, currentRegex, charSet);
                    if (stabPart.IsNonEmpty())
                        result = env.StrManager.Concat(result, stabPart);
                }

                // Append current token
                result = env.StrManager.Concat(result, token);

                // Compute derivative for next step
                if (i < chars.Count - 1)
                    currentRegex = currentRegex.Derivative(env, charSet, true);
            }
            cases.Add(result);
        }

        return env.StrManager.MkUnion(cases);
    }

    // Gets a stabilizer from regex (that cannot start with any character in excludeCharSet)
    static Str GetFilteredStabilizerStar(Environment env, Str regex, CharacterSet excludeCharSet) {
        var stabilizers = env.GetStabilizers(regex);
        if (stabilizers.Count == 0)
            return env.EmptyStr;

        List<Str> filtered = [];
        foreach (var s in stabilizers) {
            // Include s if it cannot start with any character in excludeCharSet
            if (s.Derivative(env, excludeCharSet, true).IsFail)
                filtered.Add(s);
        }

        if (filtered.Count == 0)
            return env.EmptyStr;

        return env.StrManager.MkStar(env.StrManager.MkUnion(filtered));
    }

    // Simplify along one direction (forward or backward): consume tokens and simplify powers.
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
                if (info.CurrentNode.IsZero(p1.Power, out var dep)) {
                    Reason = Reason.Merge(dep);
                    Str = info.Env.StrManager.Drop(Str, fwd);
                    continue;
                }
                if (!IsPrefixConsistent(info.CurrentNode, p1.Base, RHS, fwd)) {
                    sConstr.Add(new IntEq(info.CurrentNode.Env.ZeroInt, p1.Power, Reason));
                    return SimplifyResult.Proceed;
                }
            }

            if (SimplifyPowerSide(info, fwd))
                continue;
            break;
        }
        return SimplifyResult.Proceed;
    }

    // Main simplification and propagation routine for the regex-membership constraint.
    // Performs forward and backward simplification, handles primitive-variable cases,
    // subsumption via stabilizers, and emptiness/overapproximation checks.
    protected override SimplifyResult SimplifyAndPropagateInternal(LocalInfo info, DetModifier sConstr, ref BacktrackReasons reason) {
        while (true) {
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

            // Subsumption step: if leading variable x is subsumed by stabilizers, drop x
            if (!TrySubsume(info))
                break;
        }

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

    // Subsumption step: check if leading variable can be dropped as it is subsumed by the regex stabilizer
    bool TrySubsume(LocalInfo info) {
        if (Str.IsEmpty() || IsPrimitiveRegex())
            return false;
        if (Str.First is not NamedStrToken x)
            return false;
        if (!info.Env.HasStabilizers(Regex))
            return false;

        Str stabUnion = info.Env.GetStabilizerUnion(Regex);
        Str stabStar = info.Env.StrManager.MkStar(stabUnion);

        // Collect primitive regex constraints R^x for x
        List<Str> xConstraints = [];
        foreach (var c in info.CurrentNode.ConstraintsStrMem.Values) {
            if (!c.IsPrimitiveRegex())
                continue;
            if (c.Str.First is NamedStrToken v && v.Equals(x))
                xConstraints.Add(c.Regex);
        }

        if (xConstraints.Count == 0)
            return false;

        // Check if primitive constraints are subsumed the stabilizer
        Str xRange = info.Env.StrManager.MkIntersection(xConstraints);
        if (!info.CurrentNode.IsLanguageSubset(xRange, stabStar))
            return false;

        // Subsumption applies: drop leading x
        Log.WriteLine($"Subsumption: dropping {x} from {Str} in {Regex}");
        Str = info.Env.StrManager.DropLeft(Str);
        return true;
    }

    static int extendCnt;

    // Decide how to extend this constraint into a modifier (split, star introduction, etc.).
    public override ModifierBase? Extend(LocalInfo info, Dictionary<NamedInt, PDD<BigRational>> intSubst) {
        extendCnt++;
        // Don't sort -- this should have happened before in simplify!!
        if (IsPrimitiveRegex())
            return null;
        if (Regex.IsEmpty()) {
            Debug.Assert(!Str.IsEmpty());
            var t = Str[true];
            if (t is PowerToken p)
                return new PowerEpsilonModifier(p, Reason);
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

        // If stabilizers exist for this regex but no cycle was detected yet,
        // still try stabilizer-based decomposition for leading variables
        if (Str.First is NamedStrToken v2 && info.Env.HasStabilizers(Regex)) {
            Str stabUnion = info.Env.GetStabilizerUnion(Regex);
            if (!stabUnion.Nullable)
                return new StarIntrModifier(Id, info.CurrentNode, stabUnion, 0, Reason);
        }

        var first = Regex.FirstMinTerms();
        Debug.Assert(first.Intervals.Count > 0);

        if (Str.First is NamedStrToken v)
            return new RegexVarSplitModifier(v, first, true, Reason);
        return new RegexCharSplitModifier((SymCharToken)Str.First, first, Reason);

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

    // Convert this constraint to a Z3 Boolean expression using environment's membership function.
    public override BoolExpr ToExpr(Environment env, Dictionary<NamedStrToken, int> currentModificationCnt) => 
        (BoolExpr)env.ReMemFct.Apply(LHS.ToExpr(env, currentModificationCnt), RHS.ToExpr(env, currentModificationCnt));

    public override int GetHashCode() => 
        HashCode.Combine(LHS, RHS, History, Id) * 782620193;

    public override string ToString() => $"[{Id}] {LHS} in {RHS} : {History}";
}