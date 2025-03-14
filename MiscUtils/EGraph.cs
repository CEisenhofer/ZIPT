using System.Diagnostics;
using Microsoft.Z3;

namespace StringBreaker.MiscUtils;

class EGraph {

    readonly Dictionary<Expr, Expr> parents = [];

    public Expr Find(Expr s, UndoStack undoStack) {
        Expr r = s.Dup();
        if (parents.TryAdd(r, r)) {
            undoStack.Add(() => parents.Remove(r));
            return s;
        }
        Expr? parent = s;
        Expr? p;
        while (parents.TryGetValue(parent, out p) && !Equals(parent, p)) {
            parent = p;
        }
        if (Equals(parent, s)) 
            return parent;
        Debug.Assert(parent is not null);
        Expr? prev = parents[s].Dup();
        p = parent.Dup();
        parents[r] = p;
        undoStack.Add(() => parents[r] = prev);
        return p;
    }

    public void Merge(Expr s1, Expr s2, UndoStack undoStack) {
        var p1 = Find(s1, undoStack);
        var p2 = Find(s2, undoStack);

        Debug.Assert(!p1.Equals(p2));
        Debug.Assert(parents[p1].Equals(p1));
        Debug.Assert(parents[p2].Equals(p2));

        Expr r;
        int cmp = p1.CompareTo(p2);
        switch (cmp) {
            case < 0:
                r = p2.Dup();
                parents[r] = p1.Dup();
                undoStack.Add(() =>
                    parents[r] = r
                );
                break;
            case > 0:
                r = p1.Dup();
                parents[r] = p2.Dup();
                undoStack.Add(() =>
                    parents[r] = r
                );
                break;
            default:
                return;
        }
    }

    public Dictionary<Expr, List<Expr>> GetEClasses(UndoStack undoStack) {
        Dictionary<Expr, List<Expr>> ret = [];
        foreach (var k in parents.Keys) {
            var repr = Find(k, undoStack);
            if (!ret.TryGetValue(repr, out var lst))
                ret.Add(repr, lst = []);
            lst.Add(k);
        }
        return ret;
    }

}