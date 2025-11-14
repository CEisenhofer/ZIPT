using ZIPT.MiscUtils;
using ZIPT.Strings.Tokens;

namespace ZIPT.Constraints.Modifier;

public class RegexVarSplitModifier : DirectedNielsenModifier {
    public NamedStrToken StrVarToken { get; }
    public MinTerms Cases { get; }

    public RegexVarSplitModifier(NamedStrToken strVar, MinTerms cases, bool forward) : base(forward) {
        StrVarToken = strVar;
        Cases = cases;
    }

    public override IEnumerable<NielsenEdge> Apply(LocalInfo info) {
        // V / "" (progress)
        // V / o V & o \in r (no progress)
        var subst = new Subst(StrVarToken, info.Env.EmptyStr);
        info.CurrentNode.MkChild(info, [subst], [], [], [], true);
        yield return info.CurrentNode.Outgoing[^1];

        foreach (var @case in Cases.ToCharacterSets()) {
            if (@case.IsUnit) {
                subst = new Subst(StrVarToken,
                    info.Env.MkString(new StrToken[] { @case.First, StrVarToken }, Forwards));
                info.CurrentNode.MkChild(info, [subst], [], [], [], false);
                yield return info.CurrentNode.Outgoing[^1];
                continue;
            }
            SymCharToken sChar = info.Env.GetOrCreateSymChar(
                info.Env.GetFreshCharName(StrVarToken.Name));
            subst = new Subst(StrVarToken,
                info.Env.MkString(new StrToken[] { sChar, StrVarToken }, Forwards));
            var child = info.CurrentNode.MkChild(info, [subst], [], [], [], false);
            Log.Verify(child.AddCharConstraints(sChar, @case));
            yield return info.CurrentNode.Outgoing[^1];
        }
    }

    protected override int CompareToInternal(ModifierBase otherM) {
        RegexVarSplitModifier other = (RegexVarSplitModifier)otherM;
        int cmp = Cases.SetCount.CompareTo(other.Cases.SetCount);
        if (cmp != 0)
            return cmp;
        cmp = Cases.CharacterCount.CompareTo(other.Cases.CharacterCount);
        return cmp != 0 ? cmp : -Forwards.CompareTo(other.Forwards);
    }

    public override string ToString() {
        return $"{StrVarToken} / ε || " + string.Join(" || ", 
            Cases.ToCharacterSets().Select(range => $"{StrVarToken} in {range}"));
        //$"* {StrVarToken} / {Cases} [prefix({Cases.Base})] \\/ * {StrVarToken} / {(Forwards ? "" : StrVarToken + " ")}{Cases}{(Forwards ? " " + StrVarToken : "")}";
    }
}
