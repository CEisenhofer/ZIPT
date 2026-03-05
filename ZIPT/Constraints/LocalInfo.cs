using System.Diagnostics;
using Microsoft.Z3;
using ZIPT.MiscUtils;
using ZIPT.Strings.Chunks;
using ZIPT.Strings.Tokens;
using ZIPT.Strings.Tokens.RegexTokens;

namespace ZIPT.Constraints;

public class LocalInfo {

    // Per-search execution context. Tracks the current node/path, pushed Z3 assertions,
    // symbolic-character bookkeeping and occurrences used for regex cycle detection.


    public NielsenNode CurrentNode;
    public NielsenNode RootNode;
    public Environment Env => CurrentNode.Env;
    public Context Ctx => Env.Ctx;
    public bool OutdatedModel { get; set; } = true;
    public Dictionary<NamedStrToken, int> CurrentModificationCnt = [];
    public int ModCnt;
    public readonly Dictionary<int, NielsenEdge> CurrentPath = []; // the current path taken
    public readonly HashSet<BoolExpr> Forbidden = []; // the CDCL(T) core might block some edges
    public readonly HashSet<BoolExpr> UsedForbidden = []; // blockings that were relevant in the current run

    public List<int> LastPop = []; // for delaying asserting to Z3
    public readonly Dictionary<SymCharToken, uint> SCharPop = []; // in which push has the respective symbolic character been introduced
    public readonly List<List<(SymCharToken s, uint prev)>> SCharPopUndo = [];

    // the most recent occurrence of the given regex in the current path
    // required for regex cycle detection
    // added whenever newly added
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

    bool AssertSChar(SymCharToken c) {
        CharacterSet? s;
        if (!SCharPop.TryGetValue(c, out uint v)) {
            uint cnt = CharacterSet.MaxChar;
            if (CurrentNode.CharRanges.TryGetValue(c, out s)) {
                cnt = s.CharacterCount;
                CurrentNode.Graph.SubSolver.Add(new SetToken(s).ToIntBounds(Env, c.ToExpr(Env, CurrentModificationCnt)));
            }
            else
                CurrentNode.Graph.SubSolver.Add(new SetToken(CharacterSet.Full).ToIntBounds(Env, c.ToExpr(Env, CurrentModificationCnt)));
            SCharPop.Add(c, cnt);
            SCharPopUndo[^1].Add((c, uint.MaxValue));
            return true;
        }
        if (!CurrentNode.CharRanges.TryGetValue(c, out s))
            return false;
        uint nv = s.CharacterCount;
        if (v == nv)
            return false;
        Debug.Assert(nv < v);
        // It got refined
        SCharPop[c] = s.CharacterCount;
        SCharPopUndo[^1].Add((c, v));
        CurrentNode.Graph.SubSolver.Add(new SetToken(s).ToIntBounds(Env, c.ToExpr(Env, CurrentModificationCnt)));
        return false;
    }

    public bool DelayedAssert() => 
        DelayedAssert(CurrentNode.Graph.SubSolver, LastPop.Count == 0 ? RootNode.Id : LastPop[^1]);

    public bool DelayedAssert(Solver solver, int last) {
        if (!CurrentPath.TryGetValue(last, out NielsenEdge? e))
            return false;
        solver.Push();
        LastPop.Add(CurrentPath.Count);
        SCharPopUndo.Add([]);
        do {
            foreach (var ex in e.Asserted) {
                solver.Add(ex);
            }
            last = e.Tgt.Id;
        } while (CurrentPath.TryGetValue(last, out e));

        foreach (var kvp in CurrentNode.DisEqualities) {
            bool newC = AssertSChar(kvp.Key);
            Expr c1 = Env.ValOf.Apply(kvp.Key.ToExpr(Env, CurrentModificationCnt));
            foreach (var o in kvp.Value) {
                if (o.CompareTo(kvp.Key) < 0)
                    continue;
                Debug.Assert(!kvp.Key.Equals(o));
                if (newC || AssertSChar(o)) {
                    Expr c2 = Env.ValOf.Apply(o.ToExpr(Env, CurrentModificationCnt));
                    solver.Add(Env.Ctx.MkDistinct(c1, c2));
                }
            }
        }
        // process first the disequations because we can only detect once if the symbolic character is new
        foreach (var c in CurrentNode.CharRanges) {
            AssertSChar(c.Key);
        }

        return true;
    }

    public void DelayPop() {
        CurrentNode.Graph.SubSolver.Pop();
        LastPop.Pop();
        Debug.Assert(SCharPopUndo.IsNonEmpty());
        foreach (var (sc, prev) in SCharPopUndo[^1]) {
            if (prev == uint.MaxValue)
                SCharPop.Remove(sc);
            else
                SCharPop[sc] = prev;
        }
        SCharPopUndo.Pop();
    }
}