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
    public int ComplexityBound { get; private set; }
    public readonly Solver SubSolver; // Solver for assumption based integer reasoning
    public NielsenNode Root { get; }
    readonly HashSet<NielsenNode> nodes = [];
    public int NodeCnt => nodes.Count;
    public NielsenNode Current { get; set; }

    public NielsenGraph(OuterStringPropagator propagator) {
        Propagator = propagator;
        SubSolver = Ctx.MkSimpleSolver();
        Root = new NielsenNode(this);
        Current = Root;
        Debug.Assert(Root.Id == 0);
    }

    public bool Check() {
        if (!NielsenNode.Simplify(Root))
            return false;
        SubSolver.Assert(Root.AllIntConstraints.Select(o => o.ToExpr(this)).ToArray());
        ComplexityBound = 2;
        for (;; ComplexityBound++) {
            var res = Root.Check();
            if (res == SimplifyResult.Conflict) {
                Debug.Assert(Root.IsConflict);
                return false;
            }
            Debug.Assert(!Root.IsConflict);
            if (res == SimplifyResult.Satisfied)
                return true;
            // Depth limit encountered - retry with higher bound
        }
    }

    public void AddNode(NielsenNode node) {
        Debug.Assert(node.Id == nodes.Count);
        nodes.Add(node);
    }

    public Str? TryParseStr(Expr e) => Propagator.TryParseStr(e);

    public string ToDot() {
        StringBuilder sb = new();
        sb.AppendLine("digraph G {");
        foreach (var node in nodes) {
            sb.Append("\t")
                .Append(node.Id)
                .Append(" [label=<")
                .Append(node.ToHTMLString())
                .Append(">");
            if (node.IsConflict)
                sb.Append(", color=red");
            sb.AppendLine("];");
        }
        foreach (var node in nodes) {
            foreach (var edge in node.Outgoing ?? []) {
                sb.Append("\t")
                    .Append(node.Id)
                    .Append(" -> ")
                    .Append(edge.Tgt.Id)
                    .Append(" [label=<")
                    .Append(NielsenNode.DotEscapeStr(edge.ModStr))
                    .AppendLine(">];");
            }
        }
        sb.AppendLine("}");
        return sb.ToString();
    }

}