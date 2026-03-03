using ZIPT.MiscUtils;
using ZIPT.Strings.Tokens;

namespace ZIPT.Constraints.Modifier;

// Splits a symbolic character token into concrete or new symbolic characters according
// to regex minterms. Produces one child per minterm case.
public class RegexCharSplitModifier : ModifierBase {
    public SymCharToken SCharToken { get; }
    public MinTerms Cases { get; }

    public RegexCharSplitModifier(SymCharToken sChar, MinTerms cases, DependencyTracker reason) : base(reason) {
        SCharToken = sChar;
        Cases = cases;
    }

    public override IEnumerable<NielsenEdge> Apply(LocalInfo info) {
        // V / o V & o \in r (progress)
        foreach (var @case in Cases.ToCharacterSets()) {
            CharSubst subst;
            if (@case.IsUnit) {
                subst = new CharSubst(SCharToken, @case.First);
                info.CurrentNode.MkChild(info, [], [subst], [], [], true);
                yield return info.CurrentNode.Outgoing[^1];
                continue;
            }
            SymCharToken sChar = info.Env.GetOrCreateSymChar(
                info.Env.GetFreshCharName(SCharToken.Name));
            subst = new CharSubst(SCharToken, sChar);
            var child = info.CurrentNode.MkChild(info, [], [subst], [], [], true);
            Log.Verify(child.AddCharConstraints(sChar, @case));
            yield return info.CurrentNode.Outgoing[^1];
        }
    }

    protected override int CompareToInternal(ModifierBase otherM) {
        RegexCharSplitModifier other = (RegexCharSplitModifier)otherM;
        int cmp = Cases.SetCount.CompareTo(other.Cases.SetCount);
        return cmp != 0 ? cmp : Cases.CharacterCount.CompareTo(other.Cases.CharacterCount);
    }

    public override string ToString() {
        return string.Join(" || ", Cases.ToCharacterSets().Select(range => $"{SCharToken} in {range}"));
    }
}
