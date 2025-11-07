using ZIPT.Constraints.ConstraintElement;
using ZIPT.MiscUtils;
using ZIPT.Strings.Tokens;

namespace ZIPT.Constraints.Modifier;

public class RegexSplitModifier : DirectedNielsenModifier {
    public NamedStrToken StrVarToken { get; }
    public MinTerms Cases { get; }

    public RegexSplitModifier(NamedStrToken strVar, MinTerms cases, bool forward) : base(forward) {
        StrVarToken = strVar;
        Cases = cases;
    }

    public override IEnumerable<NielsenEdge> Apply(NielsenNode node) {
        // V / "" (progress)
        // V / o V & o \in r (no progress)
        var subst = new Subst(StrVarToken, node.Env.EmptyStr);
        node.MkChild(node, [subst], Array.Empty<Constraint>(), [], true);
        yield return node.Outgoing[^1];

        foreach (var @case in Cases.ToCharacterSets()) {
            if (@case.IsUnit) {
                subst = new Subst(StrVarToken,
                    node.Env.MkString(new StrToken[] { Cases.First, StrVarToken }, Forwards));
                node.MkChild(node, [subst], Array.Empty<Constraint>(), [], false);
                yield return node.Outgoing[^1];
                continue;
            }
            subst = new Subst(StrVarToken,
                node.Env.MkString(new StrToken[] { StrVarToken.ExtensionChar, StrVarToken }, Forwards));
            var child = node.MkChild(node, [subst], Array.Empty<Constraint>(), [], false);
            Log.Verify(child.AddCharConstraints(StrVarToken.ExtensionChar, @case));
            yield return node.Outgoing[^1];
        }
    }

    protected override int CompareToInternal(ModifierBase otherM) {
        RegexSplitModifier other = (RegexSplitModifier)otherM;
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
