using System.Diagnostics;
using ZIPT.Constraints;
using ZIPT.IntUtils;
using ZIPT.Strings.Tokens;

namespace ZIPT.Strings.Chunks;

public sealed class PowerChunk : Chunk {
    public PowerToken PowerToken { get; }

    Chunk[]? unwindFrwd;
    Chunk[]? unwindBkwd;

    public override bool IsEmpty => false;

    public override int SLength => 1;

    public override StrToken this[int idx] {
        get
        {
            Debug.Assert(idx == 0);
            return PowerToken;
        }
    }

    public PowerChunk(PowerToken powerToken, Environment env) {
        PowerToken = powerToken;
        Debug.Assert(!env.PowerChunkCache.ContainsKey(powerToken));
        env.PowerChunkCache.Add(powerToken, this);
    }

    public override Chunk DropFirstInternal(Environment env) => env.EmptyChunk;

    public override Chunk DropLastInternal(Environment env) => env.EmptyChunk;

    public override Chunk SubstX(StrVarToken x, Environment env) => this;

    public override Chunk SubstAX(StrVarToken x, CharToken a, Environment env) => this;

    public override Chunk SubstXA(StrVarToken x, CharToken a, Environment env) => this;

    public override Chunk[] SubstYX(StrVarToken x, StrVarToken y, Environment env) => [this];

    public override Chunk[] SubstXY(StrVarToken x, StrVarToken y, Environment env) => [this];

    public override Chunk[] UnwindFrwd(NielsenNode node) {
        if (unwindFrwd is not null)
            return unwindFrwd;
        unwindFrwd = new Chunk[1 + PowerToken.Base.Chunks.Count];
        for (int i = 0; i < PowerToken.Base.Chunks.Count; i++) {
            unwindFrwd[i] = PowerToken.Base.Chunks[i];
        }
        unwindFrwd[PowerToken.Base.Chunks.Count] = node.Env.GetPowerChunk(PowerToken);
        return unwindFrwd;
    }

    public override Chunk[] UnwindBkwd(NielsenNode node) {
        if (unwindBkwd is not null)
            return unwindBkwd;
        unwindBkwd = new Chunk[1 + PowerToken.Base.Chunks.Count];
        unwindBkwd[0] = node.Env.GetPowerChunk(PowerToken);
        for (int i = 0; i < PowerToken.Base.Chunks.Count; i++) {
            unwindBkwd[i + 1] = PowerToken.Base.Chunks[i];
        }
        return unwindBkwd;
    }

    public override string ToString(NielsenGraph? graph) => 
        PowerToken.ToString(graph);

    public override void AddOcc(Dictionary<StrVarToken, PDD> varOcc,
        Dictionary<CharToken, PDD> charOcc) {
        PowerToken.Base.GetOcc(out var varOcc2, out var charOcc2);
        foreach (var kvp in varOcc2) {
            var m = PDD.Mul(kvp.Value, PowerToken.Power);
            if (varOcc.TryGetValue(kvp.Key, out var count))
                varOcc[kvp.Key].Plus(m);
            else
                varOcc.Add(kvp.Key, m);
        }
    }

    public override Chunk Extract(int from, int to, Environment env) {
        Debug.Assert(0 <= from);
        Debug.Assert(from <= to);
        Debug.Assert(1 <= to);
        if (from == 0 && to == 1)
            return this;
        return env.EmptyChunk;
    }

    public override Chunk[] Apply(Interpretation itp) {
        var @base = PowerToken.Base.Apply(itp);
        if (@base.IsEmpty)
            return [];
        var p = PowerToken.Power.Apply(itp);
        if (!p.IsConst(out var val) || !val.TryGetInt(out int intVal) || intVal > Options.ModelUnwindingBound)
            return [itp.Env.GetPowerChunk(new PowerToken(@base, p))];
        Debug.Assert(!val.IsNeg);
        if (!val.IsPos)
            return [];
        var chunks = new Chunk[intVal * @base.Chunks.Count];
        for (int i = 0; i < intVal; i++) {
            for (int j = 0; j < @base.Chunks.Count; j++) {
                chunks[i * @base.Chunks.Count + j] = @base.Chunks[j];
            }
        }
        return chunks;
    }

    public override IEnumerator<StrToken> GetEnumerator() {
        yield return PowerToken;
    }

    public override IEnumerator<StrToken> GetRevEnumerator() {
        yield return PowerToken;
    }
}