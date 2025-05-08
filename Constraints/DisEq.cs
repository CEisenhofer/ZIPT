using System.Diagnostics.CodeAnalysis;
using System.Text;
using Microsoft.Z3;
using StringBreaker.Tokens;

namespace StringBreaker.Constraints;

public class DisEq {
    public SymCharToken O { get; }
    public UnitToken U { get; }

    public DisEq(SymCharToken o, UnitToken u) {
        O = o;
        U = u;
    }

    public bool SymSym => U is SymCharToken;

    public bool IsInverse([NotNullWhen(true)] out DisEq? diseq) {
        if (!SymSym) {
            diseq = null;
            return false;
        }
        diseq = new DisEq((SymCharToken)U, O);
        return true;
    }

    public BoolExpr ToExpr(NielsenGraph graph) {
        Expr e1 = O.ToExpr(graph);
        Expr e2 = U.ToExpr(graph);
        return graph.Ctx.MkNot(graph.Ctx.MkEq(e1, e2));
    }

    public override bool Equals(object? obj) =>
        obj is DisEq other && Equals(other);

    public bool Equals(DisEq other) {
        if (O.Equals(other.O) && U.Equals(other.U))
            return true;
        if (SymSym && other.SymSym)
            // o1 != o2 <==> o2 != o1
            return O.Equals((SymCharToken)other.U) && ((SymCharToken)U).Equals(other.O);
        return false;
    }

    public override int GetHashCode() =>
        // Commutative
        O.GetHashCode() ^ U.GetHashCode();

    public override string ToString() => $"{O} != {U}";
}