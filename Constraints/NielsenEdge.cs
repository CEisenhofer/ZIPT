using System.Diagnostics;
using Microsoft.Z3;
using StringBreaker.Constraints.ConstraintElement;
using StringBreaker.MiscUtils;
using StringBreaker.Tokens;

namespace StringBreaker.Constraints;

public class NielsenEdge : IEquatable<NielsenEdge> {
    public NielsenNode Src { get; }
    public BoolExpr Assumption { get; }
    public IReadOnlyList<Subst> Subst { get; }
    public IReadOnlyCollection<Constraint> SideConstraints { get; } = [];
    public IReadOnlyCollection<DisEq> DisEqConstraint { get; } = [];
    public List<BoolExpr> Asserted { get; } = [];
    public List<NamedStrToken> BumpedModCount { get; }
    public NielsenNode Tgt { get; set; }

    public string ModStr =>
        string.Join("\\n",
            Subst.Select(o => o.ToString()).
                Concat(SideConstraints.Select(o => o.ToString())).
                Concat(DisEqConstraint.Select(o => o.ToString())));

    public NielsenEdge(NielsenNode src, BoolExpr assumption, IReadOnlyList<Subst> subst, IReadOnlyCollection<Constraint> sideConds, IReadOnlyCollection<DisEq> disEqs, NielsenNode tgt) {
        Src = src;
        Assumption = assumption;
        Subst = subst;
        SideConstraints = sideConds;
        DisEqConstraint = disEqs;
        Tgt = tgt;
        BumpedModCount = [];

        foreach (var s in subst.OfType<SubstVar>()) {
            if (s.IsEliminating) 
                continue;
            Debug.Assert(!BumpedModCount.Contains(s.Var));
            BumpedModCount.Add(s.Var);
        }
    }

    public void AssertToZ3(BoolExpr e) {
        if (e.IsTrue)
            return;
        var graph = Src.Graph;
        e = graph.Ctx.MkImplies(Assumption, e);
        Asserted.Add((BoolExpr)e.Dup());
        graph.SubSolver.Assert(e);
    }

    public void IncModCount(NielsenGraph graph) {
        foreach (var b in BumpedModCount) {
            int prev = graph.CurrentModificationCnt.GetValueOrDefault(b, 0);
            graph.CurrentModificationCnt[b] = prev + 1;
        }
        graph.CurrentPath.Add(this);
        graph.ModCnt++;
    }

    public void DecModCount(NielsenGraph graph) {
        Debug.Assert(graph.ModCnt > 0);
        graph.ModCnt--;
        graph.CurrentPath.Pop();
        for (int i = BumpedModCount.Count; i > 0; i--) {
            NamedStrToken toDec = BumpedModCount[i - 1];
            int prev = graph.CurrentModificationCnt[toDec];
            Debug.Assert(prev >= 1);
            if (prev == 1)
                graph.CurrentModificationCnt.Remove(toDec);
            else
                graph.CurrentModificationCnt[toDec] = prev - 1;
        }
    }

    public NonTermSet GetNonTermModSet() {
        throw new NotImplementedException();
    }

    public override bool Equals(object? obj) =>
        obj is NielsenEdge edge && Equals(edge);

    public bool Equals(NielsenEdge? other) =>
        other is not null && Src.Equals(other.Src) && Tgt.Equals(other.Tgt);

    public override int GetHashCode() =>
        HashCode.Combine(Src, Tgt);

    public override string ToString() => 
        $"{Src} --{Subst};{string.Join(", ", SideConstraints)};{string.Join(", ", DisEqConstraint)}--> {Tgt}";
}