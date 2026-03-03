using System.Diagnostics;
using ZIPT.Constraints.ConstraintElement;
using ZIPT.IntUtils;
using ZIPT.Strings.Chunks;
using ZIPT.Strings.Tokens;

namespace ZIPT.Constraints.Modifier;

public class StarIntrModifier : ModifierBase {
    public uint Id { get; }
    public NielsenNode BackEdge { get; }
    public Str Base { get; }
    public uint DropCnt { get; }

    public StarIntrModifier(uint id, NielsenNode backEdge, Str @base, uint dropCnt, DependencyTracker reason) : base(reason) {
        Id = id;
        BackEdge = backEdge;
        Base = @base;
        DropCnt = dropCnt;
    }

    public override IEnumerable<NielsenEdge> Apply(LocalInfo info) {

        // Introduces a star-based decomposition for loop generalisation. This produces
        // alternative children that either drop a variable or split it into a star-prefixed
        // part and a remainder that is constrained not to start with the star's base.

        info.CurrentNode.Backedge = info.CurrentNode;

        Str cycle = info.Env.StrManager.MkStar(Base);

        StrVarToken pr;
        StrVarToken po = info.Env.CreateFreshStrVar("X");
        StrMem mem = info.CurrentNode.ConstraintsStrMem[Id];
        var t = mem.Str.First;

        var toAdd = new List<Constraint>(4);
        var toRemove = new List<Constraint> { mem };
        Str varDropped = info.Env.StrManager.DropLeft(mem.Str);
        var toSubst = new List<Subst>(1);

        // We can only reuse the prefix and not the postfix, because the substitution will be applied afterwards to the changed "Str"
        // Would require detecting that "pr" is subsumed by the regex on the RHS
        if (t is not StrVarToken v) {
            pr = info.Env.CreateFreshStrVar("X");
            toAdd.Add(new StrEq(info.Env.MkString(pr, po), info.Env.MkString(t), Reason));
        }
        else {
            toSubst.Add(new Subst(v, info.Env.MkString(v, po)));
            pr = v;
        }

        Debug.Assert(pr is not null && po is not null);
        Str varDroppedSubst;
        if (toSubst.Count == 1) {
            varDroppedSubst = info.Env.StrManager.Subst(varDropped, toSubst[0]);
        }
        else {
            Debug.Assert(toSubst.Count == 0);
            varDroppedSubst = varDropped;
        }
        toAdd.Add(new StrMem(
                    info.Env.StrManager.Concat(po, varDroppedSubst),
                    mem.Regex,
                    info.Env.StrManager.DropRight(mem.History, DropCnt),
                    mem.Id,
                    Reason
                )
            );
        toAdd.Add(new StrMem(info.Env.MkString(pr), cycle, info.Env.EmptyStr, info.NextRegexId++, Reason));
        var nonNullableBase = Base;
        if (nonNullableBase.Nullable) {
            // Make sure we don't have a nullable regex - otherwise this would be trivially satisfiable
            nonNullableBase = info.Env.StrManager.MkIntersection([nonNullableBase, info.Env.StrManager.MkComplement(info.Env.EmptyStr)]);
        }

        Str blocked = info.Env.StrManager.Concat(nonNullableBase, info.Env.StrManager.AllStr);
        Debug.Assert(!blocked.Nullable);
        toAdd.Add(new StrMem(info.Env.MkString(po), info.Env.StrManager.MkComplement(blocked), info.Env.EmptyStr, info.NextRegexId++, Reason));
        
        info.CurrentNode.MkChild(info, toSubst, [], toAdd, toRemove, false);
        yield return info.CurrentNode.Outgoing[^1];

        // TODO: We should rather split History than computing prefix and postfix separately
    }

    protected override int CompareToInternal(ModifierBase otherM) {
        StarIntrModifier other = (StarIntrModifier)otherM;
        int cmp = Base.CompareTo(other.Base);
        if (cmp != 0) 
            return cmp;
        cmp = Id.CompareTo(other.Id);
        return cmp != 0 ? cmp : DropCnt.CompareTo(other.DropCnt);
    }

    public override string ToString() {
        return $"[{Id}] starts with ({Base})*";
    }
}
