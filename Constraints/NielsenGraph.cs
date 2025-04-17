using Microsoft.Z3;
using System.Diagnostics;
using System.Runtime.InteropServices.ComTypes;
using System.Text;
using StringBreaker.Constraints.ConstraintElement;
using StringBreaker.MiscUtils;
using StringBreaker.Tokens;

namespace StringBreaker.Constraints;

public class NielsenGraph {

    public SaturatingStringPropagator OuterPropagator { get; }
    public Context Ctx => OuterPropagator.Ctx;
    public ExpressionCache Cache => OuterPropagator.Cache;
    public uint DepthBound { get; private set; }
    public StringPropagator InnerStringPropagator { get; }
    public readonly Solver SubSolver; // Solver for assumption based integer reasoning
    public NielsenNode Root { get; }
    public List<NielsenNode> SatNodes { get; }= [];

    public Dictionary<NamedStrToken, int> CurrentModificationCnt { get; } = [];
    public int ModCnt { get; set; }

    // all nodes
    readonly HashSet<NielsenNode> nodes = [];

    // Not required to contain all nodes (only the maximal simplified)
    readonly Dictionary<NList<StrEq>, List<NielsenNode>> subsumptionCandidates = [];
    public int NodeCnt => nodes.Count;

    public NielsenGraph(SaturatingStringPropagator outerPropagator) {
        OuterPropagator = outerPropagator;
        SubSolver = Ctx.MkSimpleSolver();
        InnerStringPropagator = new LemmaStringPropagator(SubSolver, Cache, this);
        Root = new NielsenNode(this);
        Debug.Assert(Root.Id == 0);
    }

    public bool Check() {
        SatNodes.Clear();
        if (OuterPropagator.Cancel)
            throw new SolverTimeoutException();
        if (NielsenNode.SimplifyAndInit(Root) != BacktrackReasons.Unevaluated) {
            Debug.Assert(Root.IsConflict);
            return false;
        }
        Root.AssertToZ3(Root.IntEq.Select(o => o.ToExpr(this)));
        Root.AssertToZ3(Root.IntLe.Select(o => o.ToExpr(this)));
        Root.AssertToZ3(Root.IntBounds.Select(o => o.Value.ToZ3Constraint(o.Key, this)));
        DepthBound = Options.ItDeepDepthStart;
        while (true) {
            Debug.Assert(CurrentModificationCnt.IsEmpty());
            var res = Root.Check(0);
            if (res && (!Options.FullGraphExpansion || Root.FullyExpanded))
                return true;
            if (Root.IsConflict)
                return false;
            // Depth limit encountered - retry with higher bound
            if (res)
                DepthBound += Options.ItDeepeningInc;
            else if (Root.Reason is BacktrackReasons.DepthLimit)
                DepthBound += Options.ItDeepeningInc;
            else {
                Debug.Assert(false);
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
            if (l.Subsumes(node)) {
                node.SubsumptionParent = l;
                return false;
            }
        }
        list.Add(node);
        return true;
    }

    public Str? TryParseStr(Expr e) => Cache.TryParseStr(e);

    public string ToDot() {
        List<NielsenNode> subsumed = [];
        StringBuilder sb = new();
        sb.AppendLine("digraph G {");
        foreach (var node in nodes) {
            sb.Append("\t")
                .Append(node.Id)
                .Append(" [label=\"")
                .Append(node.Id)
                .Append(": ")
                .Append(node.ToHtmlString());
            if (NielsenNode.IsActualConflict(node.Reason))
                sb.Append("\\n").Append(NielsenNode.ReasonToString(node.Reason));
            sb.Append('"');
            if (node.IsConflict)
                sb.Append(", color=red");
            if (node.IsSatisfied)
                sb.Append(", color=green");
            sb.AppendLine("];");
            if (node.SubsumptionParent is not null)
                subsumed.Add(node);
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
                if (edge.Tgt.IsConflict)
                    sb.Append(", color=red");
                sb.AppendLine("];");
            }
        }
        foreach (var s in subsumed) {
            Debug.Assert(s.SubsumptionParent is not null);
            sb.Append("\t")
                .Append(s.Id)
                .Append(" -> ")
                .Append(s.SubsumptionParent!.Id)
                .AppendLine(" [style=dotted];");
        }
        sb.AppendLine("}");
        return sb.ToString();
    }
}