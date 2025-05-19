using Microsoft.Z3;
using System.Diagnostics;
using System.Runtime.InteropServices.ComTypes;
using System.Text;
using ZIPT.Constraints.ConstraintElement;
using ZIPT.Constraints.Modifier;
using ZIPT.MiscUtils;
using ZIPT.Tokens;

namespace ZIPT.Constraints;

public class NielsenGraph {

    public SaturatingStringPropagator OuterPropagator { get; }
    public Context Ctx => OuterPropagator.Ctx;
    public ExpressionCache Cache => OuterPropagator.Cache;
    public uint DepthBound { get; private set; }
    public StringPropagator InnerStringPropagator { get; }
    public Solver SubSolver { get; } // Solver for assumption based integer reasoning
    public NielsenNode? CurrentRoot { get; private set; }

    public Dictionary<NamedStrToken, int> CurrentModificationCnt { get; } = [];
    public int ModCnt { get; set; }

    // "The number of times" we checked consistency before the last rest (on reset, we have to reset the indices of all nodes)
    public uint RunIdx { get; private set; }

    // the path to the model for sat
    public List<NielsenEdge> CurrentPath { get; } = [];

    // all nodes
    readonly HashSet<NielsenNode> nodes = [];

    // Not required to contain all nodes (only the maximal simplified)
    readonly Dictionary<NList<StrEq>, List<NielsenNode>> subsumptionCandidates = [];
    public int NodeCnt => nodes.Count;

    public NielsenGraph(SaturatingStringPropagator outerPropagator) {
        OuterPropagator = outerPropagator;
        SubSolver = Ctx.MkSimpleSolver();
        InnerStringPropagator = new LemmaStringPropagator(SubSolver, Cache, this);
        SubSolver.Push();
    }

    public void ResetCounter() {
        foreach (var node in nodes) {
            node.ResetCounter();
        }
    }

    public void ResetIndices() {
        CurrentPath.Clear();
        CurrentModificationCnt.Clear();
        ModCnt = 0;
    }

    public void ResetAll() {
        ResetIndices();
        SubSolver.Pop();
        SubSolver.Push();
    }

    public bool Check(NielsenNode root, HashSet<BoolExpr> forbidden, HashSet<BoolExpr> usedForbidden) {
        ResetAll();
        if (RunIdx == uint.MaxValue) {
            ResetCounter();
            RunIdx = 1;
        }
        else
            RunIdx++;

        if (OuterPropagator.Cancel)
            throw new SolverTimeoutException();

        CurrentRoot = root.Clone();
        NielsenNode? existing = FindExistingShallowSimplified(CurrentRoot, true);
        if (existing is not null) {
            //Debug.Assert(ReferenceEquals(PendingNode, CurrentRoot));
            //DropPending();
            CurrentRoot = existing;
        }
        if (NielsenNode.SimplifyAndInit(CurrentRoot, null) != BacktrackReasons.Unevaluated) {
            Debug.Assert(CurrentRoot.IsCurrentlyConflict);
            return false;
        }

        Debug.Assert(SubSolver is not null);

        SubSolver.Add(CurrentRoot.IntEq.Select(o => o.ToExpr(this)));
        SubSolver.Add(CurrentRoot.IntLe.Select(o => o.ToExpr(this)));
        SubSolver.Add(CurrentRoot.IntBounds.Select(o => o.Value.ToZ3Constraint(o.Key, this)));

        DepthBound = Options.ItDeepDepthStart;
        while (true) {
            Debug.Assert(CurrentPath.IsEmpty());
            Debug.Assert(CurrentModificationCnt.IsEmpty());
            var res = CurrentRoot.Check(0, forbidden, usedForbidden);
            if (OuterPropagator.Cancel)
                throw new SolverTimeoutException();
            if (res == SolveResult.SAT) {
                Debug.Assert(!CurrentRoot.IsCurrentlyConflict);
                return true;
            }
            if (res == SolveResult.UNSAT)
                return false;
            // Depth limit encountered - retry with higher bound
            DepthBound += Options.ItDeepeningInc;
        }
    }

    public void AddNode(NielsenNode node) {
        nodes.Add(node);
    }

    public NielsenNode? FindExistingShallowSimplified(NielsenNode node, bool forceRewriteAll) {
        DetModifier m = new();
        node.Simplify(new NonTermSet(), m, forceRewriteAll); // we do not do unit step propagation; just one level
        NielsenNode? existing = FindExisting(node);
        return existing;
    }

    public NielsenNode? FindExisting(NielsenNode node) {
        if (!subsumptionCandidates.TryGetValue(node.StrEq, out var list)) {
            subsumptionCandidates.Add(node.StrEq, [node]);
            return null;
        }
        foreach (var l in list) {
            if (l.Subsumes(node))
                return l;
        }
        list.Add(node);
        return null;
    }

    public Str? TryParseStr(Expr e) => Cache.TryParseStr(e);

    public string ToDot() {
        List<NielsenNode> subsumed = [];
        StringBuilder sb = new();
        sb.AppendLine("digraph G {");
        HashSet<NielsenEdge> satEdges = [];
        HashSet<NielsenNode> satNodes = [];
        foreach (var edge in CurrentPath) {
            satNodes.Add(edge.Src);
            satNodes.Add(edge.Tgt);
            satEdges.Add(edge);
        }

        foreach (var node in nodes) {
            sb.Append("\t")
                .Append(node.Id)
                .Append(" [label=\"")
                .Append(node.Id)
                .Append(": ")
                .Append(node.ToHtmlString());
            if (NielsenNode.IsActualConflict(node.CurrentReason))
                sb.Append("\\n").Append(NielsenNode.ReasonToString(node.CurrentReason));
            sb.Append('"');
            if (satNodes.Contains(node))
                sb.Append(", color=green");
            else if (node.IsGeneralConflict)
                sb.Append(", color=darkred");
            else if (!node.IsActive)
                sb.Append(", color=blue");
            else if (node.IsCurrentlyConflict)
                sb.Append(", color=red");
            sb.AppendLine("];");
        }
        foreach (var node in nodes) {
            foreach (var edge in node.Outgoing) {
                sb.Append("\t")
                    .Append(node.Id)
                    .Append(" -> ")
                    .Append(edge.Tgt.Id)
                    .Append(" [label=\"")
                    .Append(NielsenNode.DotEscapeStr(edge.ModStr))
                    .Append('"');
                if (satEdges.Contains(edge))
                    sb.Append(", color=green");
                else if (!edge.Tgt.IsActive)
                    sb.Append(", color=blue");
                else if (edge.Tgt.IsCurrentlyConflict)
                    sb.Append(", color=red");
                sb.AppendLine("];");
            }
        }
        sb.AppendLine("}");
        return sb.ToString();
    }
}