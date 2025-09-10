using System.Diagnostics;
using System.Text;
using ZIPT.Constraints;
using ZIPT.IntUtils;
using ZIPT.Strings.Tokens;

namespace ZIPT.Strings.Chunks;

public sealed class VarChunk : Chunk {
    GroundChunk Prefix { get; }
    GroundChunk Postfix { get; }
    public StrVarToken StrVarToken { get; }
    public override int SLength => Prefix.SLength + Postfix.SLength + 1;
    public override bool IsEmpty => false;

    GroundChunk? substXCache;
    readonly Dictionary<CharToken, VarChunk> substAXCache = [];
    readonly Dictionary<CharToken, VarChunk> substXACache = [];
    readonly Dictionary<StrVarToken, (VarChunk, VarChunk)> substYXCache = [];
    readonly Dictionary<StrVarToken, (VarChunk, VarChunk)> substXYCache = [];


    public override StrToken this[int idx] {
        get
        {
            Debug.Assert(idx >= 0 && idx < SLength);
            if (idx < Prefix.SLength)
                return Prefix[idx];
            if (idx == Prefix.SLength)
                return StrVarToken;
            return Postfix[idx - Prefix.SLength - 1];
        }
    }

    public VarChunk(StrVarToken strVar, GroundChunk prefix, GroundChunk postfix, Environment env) {
        Prefix = prefix;
        StrVarToken = strVar;
        Debug.Assert(prefix is not null || postfix.IsEmpty);
        Debug.Assert(!env.VarChunkCache.ContainsKey((prefix, strVar, postfix)));
        env.VarChunkCache.Add((prefix, strVar, postfix), this);
    }

    public override void OrIn(ref IdSet varOccurrences) =>
        varOccurrences.Add(StrVarToken.StrVarId);

    public override Chunk DropFirstInternal(Environment env) {
        if (Prefix.IsEmpty)
            return Postfix;
        var prefix = (GroundChunk)Prefix.DropFirst(env);
        return env.GetVarChunk(prefix, StrVarToken, Postfix);
    }

    public override Chunk DropLastInternal(Environment env) {
        if (Postfix.IsEmpty)
            return Prefix;
        var postfix = (GroundChunk)Postfix.DropLast(env);
        return env.GetVarChunk(Prefix, StrVarToken, postfix);
    }

    public override Chunk SubstX(StrVarToken x, Environment env) {
        if (!StrVarToken.Equals(x))
            return this;
        if (substXCache is not null)
            return substXCache;
        return substXCache =
            env.GetOrCreateGroundChunk(Prefix.Chars.Concat(Postfix.Chars),
                Prefix.Chars.Length + Postfix.Chars.Length);
    }

    public override Chunk SubstAX(StrVarToken x, CharToken a, Environment env) {
        if (!StrVarToken.Equals(x))
            return this;
        if (substAXCache.TryGetValue(a, out var c))
            return c;
        var prefix = env.GetOrCreateGroundChunk(Prefix.Chars.Append(a), Prefix.Chars.Length + 1);
        c = env.GetVarChunk(prefix, StrVarToken, Postfix);
        substAXCache.Add(a, c);
        return c;
    }

    public override Chunk SubstXA(StrVarToken x, CharToken a, Environment env) {
        if (!StrVarToken.Equals(x))
            return this;
        if (substXACache.TryGetValue(a, out var c))
            return c;
        var postfix = env.GetOrCreateGroundChunk(Postfix.Chars.Prepend(a), Postfix.Chars.Length + 1);
        c = env.GetVarChunk(Prefix, StrVarToken, postfix);
        substXACache.Add(a, c);
        return c;
    }

    public override Chunk[] SubstYX(StrVarToken x, StrVarToken y, Environment env) {
        if (!StrVarToken.Equals(x))
            return [this];
        if (substYXCache.TryGetValue(y, out var c))
            return [c.Item1, c.Item2];
        c = (env.GetVarChunk(Prefix, y, env.EmptyChunk),
            env.GetVarChunk(env.EmptyChunk, x, Postfix));
        substYXCache.Add(y, c);
        return [c.Item1, c.Item2];
    }

    public override Chunk[] SubstXY(StrVarToken x, StrVarToken y, Environment env) {
        if (!StrVarToken.Equals(x))
            return [this];
        if (substXYCache.TryGetValue(y, out var c))
            return [c.Item1, c.Item2];
        c = (env.GetVarChunk(Prefix, x, env.EmptyChunk),
            env.GetVarChunk(env.EmptyChunk, y, Postfix));
        substXYCache.Add(y, c);
        return [c.Item1, c.Item2];
    }

    public override Chunk[] UnwindFrwd(NielsenNode node) =>
        throw new NotSupportedException("Cannot unwind variable");

    public override Chunk[] UnwindBkwd(NielsenNode node) =>
        throw new NotSupportedException("Cannot unwind variable");

    public override string ToString(NielsenGraph? graph) {
        StringBuilder sb = new();
        foreach (var c in Prefix.Chars) {
            sb.Append(c);
        }
        sb.Append(StrVarToken.Name);
        foreach (var c in Postfix.Chars) {
            sb.Append(c);
        }
        return sb.ToString();
    }

    public override void AddOcc(Dictionary<StrVarToken, PDD> varOcc, Dictionary<CharToken, PDD> charOcc) {
        Prefix.AddOcc(varOcc, charOcc);
        if (varOcc.TryGetValue(StrVarToken, out var count))
            varOcc[StrVarToken].Plus(BigInteger.One);
        else
            varOcc[StrVarToken] = new PDD(BigInteger.One);
        Postfix.AddOcc(varOcc, charOcc);
    }

    public override Chunk Extract(int from, int to, Environment env) {
        Debug.Assert(0 <= from);
        Debug.Assert(to < SLength);
        Debug.Assert(from <= to);
        if (from == 0 && to == SLength - 1)
            return this;
        if (from < Prefix.SLength && to < Prefix.SLength)
            return Prefix.Extract(from, to, env);
        if (from > Prefix.SLength && to > Prefix.SLength)
            return Postfix.Extract(from - Prefix.SLength - 1, to - Prefix.SLength - 1, env);
        GroundChunk prefix = from < Prefix.SLength ? (GroundChunk)Prefix.Extract(from, Prefix.SLength, env) : Prefix;
        GroundChunk postfix = to > Prefix.SLength ? (GroundChunk)Postfix.Extract(0, to - Prefix.SLength - 1, env) : Postfix;
        return env.GetVarChunk(prefix, StrVarToken, postfix);
    }

    public override Chunk[] Apply(Interpretation itp) {
        var res = itp.ResolveVar(StrVarToken);
        int c = 0;
        if (Prefix.Chars.Length > 0)
            c++;
        if (Postfix.Chars.Length > 0)
            c++;
        Chunk[] chunks = new Chunk[c + res.Chunks.Count];
        c = 0;
        if (Prefix.Chars.Length > 0)
            chunks[c++] = Prefix;
        for (int i = 0; i < res.Chunks.Count; i++) {
            chunks[c++] = res.Chunks[i];
        }
        if (Postfix.Chars.Length > 0)
            chunks[c] = Postfix;
        return chunks;
    }

    public override IEnumerator<StrToken> GetEnumerator() =>
        Prefix.Append(StrVarToken).Concat(Postfix).GetEnumerator();

    public override IEnumerator<StrToken> GetRevEnumerator() {
        for (int i = Postfix.Chars.Length; i > 0; i--) {
            yield return Postfix.Chars[i - 1];
        }
        yield return StrVarToken;
        for (int i = Prefix.Chars.Length; i > 0; i--) {
            yield return Prefix.Chars[i - 1];
        }
    }
}