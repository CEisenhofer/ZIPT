namespace StringBreaker.MiscUtils;

public class UndoStack {

    readonly List<Action> undoActions = [];
    readonly List<int> undoActionsCount = [];

    public int Level => undoActionsCount.Count;

    public void Add(Action action) => 
        undoActions.Add(action);

    public void Push() =>
        undoActionsCount.Add(undoActions.Count);

    public void Pop(int cnt = 1) {
        if (cnt == 0)
            return;
        var start = undoActionsCount[^cnt];
        var end = undoActions.Count;
        for (var i = end; i > start; i--) {
            undoActions[i - 1]();
        }
        undoActions.Pop(end - start);
        undoActionsCount.Pop(cnt);
    }

    public override string ToString() =>
        $"{undoActionsCount.Count} levels [{undoActions.Count} actions]";

}