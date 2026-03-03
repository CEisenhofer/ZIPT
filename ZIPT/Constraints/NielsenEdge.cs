using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.Text.RegularExpressions;
using Microsoft.Z3;
using ZIPT.Constraints.ConstraintElement;
using ZIPT.Strings.Tokens;

namespace ZIPT.Constraints;

// Edge in the Nielsen graph representing a transition caused by substitutions and side-constraints.
// Carries the asserted Z3 lemmas for the edge and bookkeeping for modification counts.
public class NielsenEdge : IEquatable<NielsenEdge> {
    public NielsenNode Src { get; }
    public IReadOnlyList<Subst> Subst { get; }
    public IReadOnlyList<CharSubst> SubstC { get; }
    public IReadOnlyCollection<Constraint> SideConstraints { get; }
    public List<BoolExpr> Asserted { get; } = [];
    public List<NamedStrToken> BumpedModCount { get; }
    public NielsenNode Tgt { get; set; }

    public string ModStr =>
        string.Join("\\n",
            Subst.Select(o => o.ToString()).Concat(
                SubstC.Select(o => o.ToString()).Concat(
                    SideConstraints.Select(o => o.ToString()))));

    public NielsenEdge(NielsenNode src, IReadOnlyList<Subst> subst, IReadOnlyList<CharSubst> substC,
        IReadOnlyCollection<Constraint> sideConds, NielsenNode tgt) {
        Src = src;
        Subst = subst;
        SubstC = substC;
        SideConstraints = sideConds;
        Tgt = tgt;
        BumpedModCount = [];

        foreach (var s in subst) {
            if (s.IsEliminating) 
                continue;
            Debug.Assert(!BumpedModCount.Contains(s.Var));
            BumpedModCount.Add(s.Var);
        }
    }

    public void AddZ3Constraint(BoolExpr e) {
        if (e.IsTrue)
            return;
        Asserted.Add((BoolExpr)e.Dup());
    }

    public void IncModCount(LocalInfo info) {
        foreach (var b in BumpedModCount) {
            int prev = info.CurrentModificationCnt.GetValueOrDefault(b, 0);
            info.CurrentModificationCnt[b] = prev + 1;
        }
        info.CurrentPath.Add(Src.Id, this);
        info.ModCnt++;
        info.CurrentNode = Tgt;
    }

    public void DecModCount(LocalInfo info) {
        Debug.Assert(info.ModCnt > 0);
        info.ModCnt--;
        info.CurrentPath.Remove(Src.Id);
        for (int i = BumpedModCount.Count; i > 0; i--) {
            NamedStrToken toDec = BumpedModCount[i - 1];
            int prev = info.CurrentModificationCnt[toDec];
            Debug.Assert(prev >= 1);
            if (prev == 1)
                info.CurrentModificationCnt.Remove(toDec);
            else
                info.CurrentModificationCnt[toDec] = prev - 1;
        }
        Debug.Assert(ReferenceEquals(info.CurrentNode, Tgt));
        info.CurrentNode = Src;
    }

    public override bool Equals(object? obj) =>
        obj is NielsenEdge edge && Equals(edge);

    public bool Equals(NielsenEdge? other) =>
        other is not null && Src.Equals(other.Src) && Tgt.Equals(other.Tgt);

    public override int GetHashCode() =>
        HashCode.Combine(Src, Tgt);

    public override string ToString() => 
        $"{Src} --[{string.Join(", ", Subst)};{string.Join(", ", SubstC)};{string.Join(", ", SideConstraints)}]--> {Tgt}";
}