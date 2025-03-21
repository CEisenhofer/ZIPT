using Microsoft.Z3;
using System.Diagnostics;
using System.Runtime.InteropServices.ComTypes;
using System.Text;
using StringBreaker.Constraints.ConstraintElement;
using StringBreaker.MiscUtils;

namespace StringBreaker.Constraints;

public class NielsenGraph {

    public OuterStringPropagator Propagator { get; }
    public Context Ctx => Propagator.Ctx;
    public uint DepthBound { get; private set; }
    public uint ComplexityBound { get; private set; }
    public readonly Solver SubSolver; // Solver for assumption based integer reasoning
    public NielsenNode Root { get; }
    public List<NielsenNode> SatNodes { get; }= [];

    // all nodes
    readonly HashSet<NielsenNode> nodes = [];

    // Not required to contain all nodes (only the maximal simplified)
    readonly Dictionary<StrConstraintSet<StrEq>, List<NielsenNode>> subsumptionCandidates = [];
    public int NodeCnt => nodes.Count;

    public NielsenGraph(OuterStringPropagator propagator) {
        Propagator = propagator;
        SubSolver = Ctx.MkSimpleSolver();
        Root = new NielsenNode(this);
        Debug.Assert(Root.Id == 0);
    }

    public bool Check() {
        if (NielsenNode.Simplify(Root) != BacktrackReasons.Unevaluated)
            return false;
        SubSolver.Assert(Root.AllIntConstraints.Select(o => o.ToExpr(this)).ToArray());
        DepthBound = Options.ItDeepDepthStart;
        ComplexityBound = Options.ItDeepComplexityStart;
        while (true) {
            var res = Root.Check(0, 0);
            if (res && (!Options.FullGraphExpansion || Root.FullyExpanded))
                return true;
            if (Root.IsConflict)
                return false;
            // Depth limit encountered - retry with higher bound
            if (res) {
                DepthBound += Options.ItDeepeningInc;
                ComplexityBound += Options.ItDeepeningInc;
            }
            else if (Root.Reason is BacktrackReasons.DepthLimit or BacktrackReasons.BothLimits)
                DepthBound += Options.ItDeepeningInc;
            else {
                Debug.Assert(Root.Reason == BacktrackReasons.ComplexityLimit);
                ComplexityBound += Options.ItDeepeningInc;
            }
        }
    }

    public void AddNode(NielsenNode node) {
        Debug.Assert(node.Id == nodes.Count);
        nodes.Add(node);
    }

    public bool AddSumbsumptionCandidate(NielsenNode node) {
        if (!subsumptionCandidates.TryGetValue(node.StrEq, out var list)) {
            subsumptionCandidates.Add(node.StrEq, [node]);
            return true;
        }
        foreach (var l in list) {
            if (l.Subsumes(node))
                return false;
        }
        list.Add(node);
        return true;
    }

    public Str? TryParseStr(Expr e) => Propagator.TryParseStr(e);

    public string ToDot() {
        StringBuilder sb = new();
        sb.AppendLine("digraph G {");
        foreach (var node in nodes) {
            sb.Append("\t")
                .Append(node.Id)
                .Append(" [label=\"")
                .Append(node.Id)
                .Append(": ")
                .Append(node.ToHTMLString());
            if (NielsenNode.IsActualConflict(node.Reason))
                sb.Append("\\n").Append(NielsenNode.ReasonToString(node.Reason));
            sb.Append('"');
            if (node.IsConflict)
                sb.Append(", color=red");
            if (node.IsSatisfied)
                sb.Append(", color=green");
            sb.AppendLine("];");
        }
        foreach (var node in nodes) {
            foreach (var edge in node.Outgoing ?? []) {
                sb.Append("\t")
                    .Append(node.Id)
                    .Append(" -> ")
                    .Append(edge.Tgt.Id)
                    .Append(" [label=\"")
                    .Append(NielsenNode.DotEscapeStr(edge.ModStr))
                    .AppendLine("\"];");
            }
        }
        sb.AppendLine("}");
        return sb.ToString();
    }
}