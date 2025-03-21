using System.Diagnostics;
using StringBreaker.IntUtils;
using StringBreaker.MiscUtils;
using StringBreaker.Tokens;

namespace StringBreaker.Constraints.ConstraintElement;

public abstract class StrEqBase : StrConstraint, IComparable<StrEqBase> {
    public Str LHS { get; protected set; }
    public Str RHS { get; protected set; }

    protected StrEqBase(Str lhs, Str rhs) {
        LHS = lhs;
        RHS = rhs;
        SortStr();
    }

    public override bool Equals(object? obj) => obj is StrEqBase other && Equals(other);
    public bool Equals(StrEqBase? other) => CompareTo(other) == 0;

    static readonly Dictionary<Type, int> TokenTypeOrder = new() {
        { typeof(PowerToken), 0 },
        { typeof(SymCharToken), 1 },
        { typeof(CharToken), 2 },
        { typeof(StrVarToken), 3 },
    };

    protected void SortStr() {
        Str s1 = LHS, s2 = RHS;
        SortStr(ref s1, ref s2, true);
        LHS = s1;
        RHS = s2;
    }

    protected static void SortStr(ref Str s1, ref Str s2, bool dir) {
        if (s1.IsEmpty())
            return;
        if (s2.IsEmpty()) {
            (s1, s2) = (s2, s1);
            return;
        }
        Debug.Assert(s1.Count > 0);
        Debug.Assert(s2.Count > 0);

        if (TokenTypeOrder[s1.Peek(dir).GetType()] > TokenTypeOrder[s2.Peek(dir).GetType()])
            (s1, s2) = (s2, s1);
        Debug.Assert(TokenTypeOrder[s1.Peek(dir).GetType()] <= TokenTypeOrder[s2.Peek(dir).GetType()]);
    }

    public override void Apply(Subst subst) {
        LHS = LHS.Apply(subst);
        RHS = RHS.Apply(subst);
    }

    public override void Apply(Interpretation itp) {
        LHS = LHS.Apply(itp);
        RHS = RHS.Apply(itp);
    }

    public override void CollectSymbols(HashSet<StrVarToken> vars, HashSet<SymCharToken> sChars, 
        HashSet<IntVar> iVars, HashSet<CharToken> alphabet) {
        LHS.CollectSymbols(vars, sChars, iVars, alphabet);
        RHS.CollectSymbols(vars, sChars, iVars, alphabet);
    }

    public override bool Contains(StrVarToken v) =>
        LHS.Any(o => o.RecursiveIn(v)) || RHS.Any(o => o.RecursiveIn(v));

    public int CompareTo(StrEqBase? other) {
        if (other is null)
            return 1;
        int cmp = LHS.CompareTo(other.LHS);
        return cmp != 0 ? cmp : RHS.CompareTo(other.RHS);
    }
}
