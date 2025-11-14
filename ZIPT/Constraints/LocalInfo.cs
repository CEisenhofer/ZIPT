using Microsoft.Z3;
using ZIPT.MiscUtils;
using ZIPT.Strings.Chunks;
using ZIPT.Strings.Tokens;

namespace ZIPT.Constraints;

public class LocalInfo {

    public NielsenNode CurrentNode;
    public NielsenNode RootNode;
    public Environment Env => CurrentNode.Env;
    public Context Ctx => Env.Ctx;
    public Dictionary<NamedStrToken, int> CurrentModificationCnt = [];
    public int ModCnt;
    public readonly Dictionary<int, NielsenEdge> CurrentPath = []; // the current path taken
    public readonly HashSet<BoolExpr> Forbidden = []; // the CDCL(T) core might block some edges
    public readonly HashSet<BoolExpr> UsedForbidden = []; // blockings that were relevant in the current run
    // the most recent occurrence of the given regex in the current path
    // required for regex cycle detection
    // added whenever newly added
    public List<int> LastPop = [];
    public readonly Dictionary<(Str regex, uint id), int> RegexOccurrence = [];
    public uint NextRegexId = 0;

    public LocalInfo(NielsenNode currentNode) {
        CurrentNode = currentNode;
        RootNode = currentNode;
    }

    public LocalInfo(NielsenNode currentNode, HashSet<BoolExpr> forbidden) {
        CurrentNode = currentNode;
        RootNode = currentNode;
        Forbidden = forbidden;
    }

    public bool DelayedAssert() {
        int last = LastPop.Count == 0 ? RootNode.Id : LastPop[^1];
        if (!CurrentPath.TryGetValue(last, out NielsenEdge? e))
            return false;
        CurrentNode.Graph.SubSolver.Push();
        LastPop.Add(CurrentPath.Count);
        do {
            foreach (var ex in e.Asserted) {
                CurrentNode.Graph.SubSolver.Add(ex);
            }
            last = e.Tgt.Id;
        } while (CurrentPath.TryGetValue(last, out e));
        return true;
    }

    public void DelayPop() {
        CurrentNode.Graph.SubSolver.Pop();
        LastPop.Pop();
    }
}