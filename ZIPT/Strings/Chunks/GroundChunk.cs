using System.Diagnostics;
using System.Text;
using ZIPT.Constraints;
using ZIPT.IntUtils;
using ZIPT.Strings.Tokens;

namespace ZIPT.Strings.Chunks;

public sealed class GroundChunk : Chunk {
    // TODO: Cache occurrence counts?
    public CharToken[] Chars { get; }

    public override bool IsEmpty => Chars.Length == 0;
    public override int SLength => Chars.Length;

    public override StrToken this[int idx] {
        get
        {
            Debug.Assert(idx >= 0 && idx < SLength);
            return Chars[idx];
        }
    }

    public GroundChunk(CharToken[] chars) {
        Chars = chars;
    }

    public override Chunk DropFirstInternal(Environment env) {
        if (IsEmpty)
            throw new NotSupportedException("String is empty");
        return env.GetOrCreateGroundChunk(Chars[1..]);
    }

    public override Chunk DropLastInternal(Environment env) {
        if (IsEmpty)
            throw new NotSupportedException("String is empty");
        return env.GetOrCreateGroundChunk(Chars[..^1]);
    }

    public override Chunk SubstX(StrVarToken x, Environment env) => this;
    public override Chunk SubstAX(StrVarToken x, CharToken a, Environment env) => this;
    public override Chunk SubstXA(StrVarToken x, CharToken a, Environment env) => this;

    public override Chunk[] SubstYX(StrVarToken x, StrVarToken y, Environment env) => [this];
    public override Chunk[] SubstXY(StrVarToken x, StrVarToken y, Environment env) => [this];

    public override Chunk[] UnwindFrwd(NielsenNode node) =>
        throw new NotSupportedException("Cannot unwind constant");

    public override Chunk[] UnwindBkwd(NielsenNode node) =>
        throw new NotSupportedException("Cannot unwind constant");

    public override string ToString() {
        StringBuilder sb = new();
        foreach (var c in Chars) {
            sb.Append(c);
        }
        return sb.ToString();
    }

    public override string ToString(NielsenGraph? graph) {
        StringBuilder sb = new();
        foreach (var c in Chars) {
            sb.Append(c);
        }
        return sb.ToString();
    }

    public override void AddOcc(
        Dictionary<StrVarToken, PDD> varOcc,
        Dictionary<CharToken, PDD> charOcc) {
        foreach (var c in Chars) {
            charOcc.Add(c, new PDD(BigInteger.One));
        }
    }

    public override Chunk Extract(int from, int to, Environment env) {
        Debug.Assert(0 <= from);
        Debug.Assert(to < SLength);
        Debug.Assert(from <= to);
        if (from == 0 && to == SLength - 1)
            return this;
        return env.GetOrCreateGroundChunk(Chars[from..to]);
    }

    public override Chunk[] Apply(Interpretation itp) => [this];

    public override IEnumerator<StrToken> GetEnumerator() => Chars.OfType<StrToken>().GetEnumerator();
    public override IEnumerator<StrToken> GetRevEnumerator() {
        for (int i = Chars.Length; i > 0; i--) {
            yield return Chars[i - 1];
        }
    }

}