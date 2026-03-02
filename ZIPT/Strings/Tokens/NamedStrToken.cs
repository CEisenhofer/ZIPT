using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.Numerics;
using ZIPT.Constraints;
using ZIPT.Constraints.ConstraintElement;
using ZIPT.IntUtils;
using ZIPT.MiscUtils;

namespace ZIPT.Strings.Tokens;

public abstract class NamedStrToken : StrToken {

    public uint StrVarId { get; } // TODO: Use for easier containment checks

    public abstract string OriginalName { get; }
    public string Name => Aux ? $"{OriginalName}${ChildIdx}" : OriginalName;
    public bool Aux => ChildIdx != 0;
    public RefInt ChildCnt { get; } // Keep track of how many children this token has
    public int ChildIdx { get; } // The id of this child of the token
    public NamedStrToken? Parent { get; } // The direct parent of this token
    protected NamedStrToken? Extension1 { get; set; } // x' for extension. e.g. x / ax' or x / x'a
    protected NamedStrToken? Extension2 { get; set; } // x'' in this unlikely case we need to split it up. e.g., x = x'x''
    protected SymCharToken? extensionChar; // for unwinding regexes
    IntVar? PowerExtension { get; set; } // The unique power constant n used when eliminating a variable x / u^n u'

    public override bool Ground => false;
    public override bool RegexFree => true;
    public override bool Derivable => false;
    public override bool Nullable => false;
    public override bool BasicRegex => true;
    protected NamedStrToken(NamedStrToken parent) {
        Parent = parent;
        ChildCnt = parent.ChildCnt;
        ChildIdx = ChildCnt.Inc();
        Debug.Assert(ChildIdx > 0);
    }

    protected NamedStrToken() {
        ChildIdx = 0;
        ChildCnt = new RefInt(1);
        Parent = null;
    }

    [Pure]
    public abstract NamedStrToken GetExtension1();
    [Pure]
    public abstract NamedStrToken GetExtension2();

    [Pure]
    public IntVar GetPowerExtension() => 
        PowerExtension ??= new IntVar();

    public sealed override List<StrDecomposition> GetDecomposition(NielsenNode node, bool fwd) {
        // P(x) := y with x = yz, |y| < |x|
        // TODO
        NamedStrToken y = GetExtension1();
        NamedStrToken z = GetExtension2();
        var yl = LenVar.MkLenPoly(y, node.Env);
        var xl = LenVar.MkLenPoly(this, node.Env);
        yl = yl.Add(BigInteger.One);
        if (fwd)
            return [new StrDecomposition(node.Env.MkString(y), node.Env.MkString(z), [new IntLe(yl, xl, new DependencyTracker(0))], new Subst(this, node.Env.MkString(y, z)))];
        return [new StrDecomposition(node.Env.MkString(y), node.Env.MkString(z), [new IntLe(yl, xl, new DependencyTracker(0))], new Subst(this, node.Env.MkString(z, y)))];
    }

    protected sealed override int CompareToInternal(StrToken other) {
        Debug.Assert(other is NamedStrToken);
        int cmp = string.Compare(Name, ((NamedStrToken)other).Name, StringComparison.Ordinal);
        return cmp != 0 ? cmp : ChildIdx.CompareTo(((NamedStrToken)other).ChildIdx);
    }

    public override void CollectSymbols(NonTermSet nonTermSet, CharacterSet alphabet) => 
        nonTermSet.Add(this);

    public override bool Equals(StrToken? other) =>
        other is NamedStrToken token && Equals(token);

    public bool Equals(NamedStrToken other) =>
        ChildIdx.Equals(other.ChildIdx) && Name.Equals(other.Name, StringComparison.Ordinal);

    public override int GetHashCode() => HashCode.Combine(GetType(), Name, ChildCnt);

    public override string ToString(NielsenGraph? graph) => Name;
}