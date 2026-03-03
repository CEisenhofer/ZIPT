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

        // This split on
        // x \in base*
        // drop x
        // OR
        // x / x' x'' 
        // x' \in base*
        // x'' \notin base.*
        // |x''| > 0
        // drop x'

        info.CurrentNode.Backedge = info.CurrentNode;

        Debug.Assert(!Base.Nullable);
        Str cycle = info.Env.StrManager.MkStar(Base);

        // Self-stabilization: S(cycle) := { cycle }
        info.Env.AddStabilizer(cycle, cycle);

        StrVarToken pr;
        StrVarToken po = info.Env.CreateFreshStrVar("X");
        StrMem mem = info.CurrentNode.ConstraintsStrMem[Id];
        var t = mem.Str.First;

        var toAdd = new List<Constraint>(4);
        var toRemove = new List<Constraint> { mem };
        // TODO: Check other mem-constraints with the same history and variable to eliminate both simultaniously
        Str newHistory = info.Env.StrManager.Concat(info.Env.StrManager.DropRight(mem.History, DropCnt), cycle);
        Str varDropped = info.Env.StrManager.DropLeft(mem.Str);

        Debug.Assert(!mem.IsPrimitiveRegex());
        toAdd.Add(new StrMem(varDropped, mem.Regex, newHistory, mem.Id, Reason));
        toAdd.Add(new StrMem(info.Env.MkString(t), cycle, info.Env.EmptyStr, info.NextRegexId++, Reason));

        info.CurrentNode.MkChild(info, [], [], toAdd, toRemove, true);
        yield return info.CurrentNode.Outgoing[^1];

        toAdd.Clear();
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
                    info.Env.StrManager.Concat(info.Env.StrManager.DropRight(mem.History, DropCnt), cycle),
                    mem.Id,
                    Reason
                )
            );
        toAdd.Add(new StrMem(info.Env.MkString(pr), cycle, info.Env.EmptyStr, info.NextRegexId++, Reason));
        Str blocked = info.Env.StrManager.Concat(Base, info.Env.StrManager.AllStr);
        Debug.Assert(!blocked.Nullable);
        toAdd.Add(new StrMem(info.Env.MkString(po), info.Env.StrManager.MkComplement(blocked), info.Env.EmptyStr, info.NextRegexId++, Reason));
        toAdd.Add(IntLe.MkLt(info.Env.ZeroInt, LenVar.MkLenPoly([po], info.Env), Reason));

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
