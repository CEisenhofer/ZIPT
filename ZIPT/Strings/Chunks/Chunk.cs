using System.Collections;
using System.Diagnostics;
using Microsoft.Z3;
using ZIPT.Constraints;
using ZIPT.IntUtils;
using ZIPT.Strings.Tokens;

namespace ZIPT.Strings.Chunks;

public abstract class Chunk : IEnumerable<StrToken> {


    Chunk? dropForwardCache;
    Chunk? dropBackwardCache;
    public abstract bool IsEmpty { get; }
    public abstract int SLength { get; }

    // the hash code and equality is the default reference one

    public abstract StrToken this[int idx] {
        get;
    }

    public Chunk DropFirst(Environment env) {
        if (dropForwardCache is not null)
            return dropForwardCache;
        return dropForwardCache = DropFirstInternal(env);
    }
    public abstract Chunk DropFirstInternal(Environment env);

    public Chunk DropLast(Environment env) {
        if (dropBackwardCache is not null)
            return dropBackwardCache;
        return dropBackwardCache = DropLastInternal(env);
    }
    public abstract Chunk DropLastInternal(Environment env);

    public abstract Chunk SubstX(StrVarToken x, Environment env);
    public abstract Chunk SubstAX(StrVarToken x, CharToken a, Environment env);
    public abstract Chunk SubstXA(StrVarToken x, CharToken a, Environment env);
    public abstract Chunk[] SubstYX(StrVarToken x, StrVarToken y, Environment env);
    public abstract Chunk[] SubstXY(StrVarToken x, StrVarToken y, Environment env);

    public abstract Chunk[] UnwindFrwd(NielsenNode node);
    public abstract Chunk[] UnwindBkwd(NielsenNode node);

    public abstract void AddOcc(Dictionary<StrVarToken, PDD> varOcc, Dictionary<CharToken, PDD> charOcc);

    public abstract Chunk Extract(int from, int to, Environment env);

    public abstract Chunk[] Apply(Interpretation itp);
    
    public Expr ToExpr(NielsenGraph graph) {
        if (IsEmpty)
            return graph.Env.Epsilon;
        using var e = GetRevEnumerator();
        if (!e.MoveNext()) {
            Debug.Assert(false);
            return graph.Env.Epsilon;
        }
        Expr last = e.Current.ToExpr(graph);
        while (e.MoveNext()) {
            last = graph.Env.MkConcat(e.Current.ToExpr(graph), last);
        }
        return last;
    }

    public abstract IEnumerator<StrToken> GetEnumerator();
    IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();
    public abstract IEnumerator<StrToken> GetRevEnumerator();
    public sealed override string ToString() => ToString(null);
    public abstract string ToString(NielsenGraph? graph);
    public virtual void OrIn(ref IdSet varOccurrences) { }
}