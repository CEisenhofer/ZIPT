using Microsoft.Z3;
using System.Diagnostics;
using System.Numerics;
using System.Runtime.InteropServices.ComTypes;
using System.Text;
using System.Xml.Linq;
using ZIPT.Constraints.ConstraintElement;
using ZIPT.Constraints.Modifier;
using ZIPT.IntUtils;
using ZIPT.MiscUtils;
using ZIPT.Strings.Chunks;
using ZIPT.Strings.Tokens;

namespace ZIPT.Constraints;

public class NielsenGraph {

    public SaturatingStringPropagator OuterPropagator { get; }
    public Context Ctx => OuterPropagator.Ctx;
    public Environment Env => OuterPropagator.Env;
    public uint DepthBound { get; private set; }
    public StringPropagator InnerStringPropagator { get; }
    public Solver SubSolver { get; } // Solver for assumption based integer reasoning
    public NielsenNode? InitRoot { get; private set; }

    // "The number of times" we checked consistency before the last rest (on reset, we have to reset the indices of all nodes)
    public uint RunIdx { get; private set; }


    // all nodes
    readonly HashSet<NielsenNode> nodes = [];

    // Not required to contain all nodes (only the maximal simplified)
    readonly Dictionary<NList<StrEq>, List<NielsenNode>> subsumptionCandidates = [];
    public int NodeCnt => nodes.Count;

    public NielsenGraph(SaturatingStringPropagator outerPropagator) {
        OuterPropagator = outerPropagator;
        SubSolver = Ctx.MkSimpleSolver();
        InnerStringPropagator = new LemmaStringPropagator(SubSolver, Env, this);
        SubSolver.Push();
    }

    public void ResetCounter() {
        foreach (var node in nodes) {
            node.ResetCounter();
        }
    }

    public void ResetAll() {
        SubSolver.Pop();
        SubSolver.Push();
    }

    public bool Check(LocalInfo info) {
        ResetAll();
        if (RunIdx == uint.MaxValue) {
            ResetCounter();
            RunIdx = 1;
        }
        else
            RunIdx++;

        if (OuterPropagator.Cancel)
            throw new SolverTimeoutException();

        /*NielsenNode? existing = FindExisting(info.CurrentNode);
        if (existing is null) {
            info.CurrentNode = InitRoot = info.CurrentNode.Clone();
            if (NielsenNode.SimplifyAndInit(info, null) != BacktrackReasons.Unevaluated) {
                Debug.Assert(info.CurrentNode.IsCurrentlyConflict);
                return false;
            }
            existing = FindExisting(info.CurrentNode);
            if (existing is not null) {
                //Debug.Assert(ReferenceEquals(PendingNode, CurrentRoot));
                //DropPending();
                info.CurrentNode = existing;
            }
        }
        else
            info.CurrentNode = InitRoot = existing;*/
        // For now, do not try to cache existing
        info.CurrentNode = InitRoot = info.CurrentNode.Clone();
        if (NielsenNode.SimplifyAndInit(info, null) != BacktrackReasons.Unevaluated) {
            Debug.Assert(info.CurrentNode.IsCurrentlyConflict);
            return false;
        }
        //

        info.RootNode = info.CurrentNode;

        Debug.Assert(SubSolver is not null);

        SubSolver.Add(info.CurrentNode.ConstraintsIntEq.Select(o => o.ToExpr(info)));
        SubSolver.Add(info.CurrentNode.ConstraintsIntLe.Select(o => o.ToExpr(info)));
        SubSolver.Add(info.CurrentNode.IntBounds.Select(o => 
            Interval<BigInteger>.ToZ3Constraint(o.Value, o.Key, info)));

        DepthBound = Options.ItDeepDepthStart;
        int pathCnt = info.CurrentPath.Count;
        int modCnt = info.CurrentModificationCnt.Count;

        while (true) {
            Debug.Assert(info.CurrentPath.Count == pathCnt);
            Debug.Assert(info.CurrentModificationCnt.Count == modCnt);
            var res = info.CurrentNode.Check(0, info);
            Debug.Assert(res != SolveResult.CYCLIC);
            if (OuterPropagator.Cancel)
                throw new SolverTimeoutException();
            if (res == SolveResult.SAT) {
                Debug.Assert(!info.CurrentNode.IsCurrentlyConflict);
                if (Options.OutputGraph)
                    Console.WriteLine(ToDot(info));
                return true;
            }
            if (res == SolveResult.UNSAT) {
                if (Options.OutputGraph)
                    Console.WriteLine(ToDot(info));
                return false;
            }
            // Depth limit encountered - retry with higher bound
            DepthBound += Options.ItDeepeningInc;
        }
    }

    public void AddNode(NielsenNode node) {
        nodes.Add(node);
    }

    public NielsenNode? FindExisting(NielsenNode node) {
        if (!subsumptionCandidates.TryGetValue(node.ConstraintsStrEq, out var list)) {
            subsumptionCandidates.Add(node.ConstraintsStrEq, [node]);
            return null;
        }
        foreach (var l in list) {
            if (l.Subsumes(node))
                return l;
        }
        list.Add(node);
        return null;
    }

    public Str? TryParseStr(Expr e) => Env.TryParseStr(e);

    public string ToDot(LocalInfo? info = null) {
        StringBuilder sb = new();
        sb.AppendLine("digraph G {");
        HashSet<NielsenEdge> satEdges = [];
        HashSet<NielsenNode> satNodes = [];
        foreach (var edge in info?.CurrentPath ?? []) {
            satNodes.Add(edge.Value.Src);
            satNodes.Add(edge.Value.Tgt);
            satEdges.Add(edge.Value);
        }

        foreach (var node in nodes) {
            sb.Append('\t')
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
                sb.Append('\t')
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
            if (node.Backedge is not null) {
                sb.Append('\t')
                    .Append(node.Id)
                    .Append(" -> ")
                    .Append(node.Backedge.Id)
                    .AppendLine(" [style=dotted];");
            }
        }
        sb.AppendLine("}");
        return sb.ToString();
    }
}