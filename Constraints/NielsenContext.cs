using System.Diagnostics;
using StringBreaker.Constraints.ConstraintElement;
using StringBreaker.IntUtils;
using StringBreaker.MiscUtils;
using StringBreaker.Strings.Tokens;

namespace StringBreaker.Constraints;

public class NielsenContext {
    public NielsenNode CurrentNode { get; set; }
    public NielsenGraph Graph => CurrentNode.Graph;
    public ExpressionCache Cache => Graph.Cache;
    public List<NielsenEdge> Edges { get; } = [];

    public NielsenContext(NielsenNode currentNode) {
        CurrentNode = currentNode;
    }

    public void Push(NielsenEdge edge) {
        Edges.Add(edge);
        CurrentNode = edge.Tgt;
    }

    public void Pop() {
        Debug.Assert(Edges.IsNonEmpty());
        CurrentNode = Edges[^1].Src;
        Edges.Pop();
    }

    public void Pop(int cnt) {
        // TODO: Improve
        for (int i = 0; i < cnt; i++) {
            Pop();
        }
    }

    public bool IsEq(Poly lhs, Poly rhs) => CurrentNode.IsEq(lhs, rhs);
    public bool IsPowerElim(Poly p) => CurrentNode.IsPowerElim(p);
    public bool IsZero(Poly p) => CurrentNode.IsZero(p);
    public bool IsOne(Poly p) => CurrentNode.IsOne(p);
    public bool IsLe(Poly lhs, Poly rhs) => CurrentNode.IsLe(lhs, rhs);
    public bool IsLt(Poly lhs, Poly rhs) => CurrentNode.IsLt(lhs, rhs);
    public bool IsNeg(Poly p) => CurrentNode.IsNeg(p); 
    public bool IsNonPos(Poly p) => CurrentNode.IsNonPos(p);
    public bool IsPos(Poly p) => CurrentNode.IsPos(p);
    public bool IsNonNeg(Poly p) => CurrentNode.IsNonNeg(p);
    public bool AreDiseq(UnitToken u1, UnitToken u2) => CurrentNode.AreDiseq(u1, u2);
}