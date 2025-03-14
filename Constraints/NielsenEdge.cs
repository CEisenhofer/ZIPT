using System.Collections.Generic;
using System.Diagnostics;
using Microsoft.Z3;
using StringBreaker.Constraints.ConstraintElement;
using StringBreaker.Constraints.Modifier;
using StringBreaker.MiscUtils;

namespace StringBreaker.Constraints;

public class NielsenEdge : IEquatable<NielsenEdge> {
    public NielsenNode Src { get; }
    public BoolExpr Assumption { get; }
    public IReadOnlyList<Subst> Subst { get; }
    public HashSet<Constraint> SideConstraints { get; } = [];
    public NielsenNode Tgt { get; }

    public string ModStr
    {
        get
        {
            if (Subst.Count == 0) {
                if (SideConstraints.IsEmpty())
                    return "";
                return string.Join("\\n", SideConstraints);
            }
            if (SideConstraints.IsEmpty())
                return string.Join("\\n", Subst.Select(o => o.ToString()));
            return string.Join("\\n", Subst.Select(o => o.ToString()).Concat(SideConstraints.Select(o => o.ToString())));
        }
    }

    public NielsenEdge(NielsenNode src, BoolExpr assumption, IReadOnlyList<Subst> subst, NielsenNode tgt) {
        Src = src;
        Assumption = assumption;
        Subst = subst;
        Tgt = tgt;
    }

    public override bool Equals(object? obj) =>
        obj is NielsenEdge edge && Equals(edge);

    public bool Equals(NielsenEdge? other) =>
        other is not null && Src.Equals(other.Src) && Tgt.Equals(other.Tgt);

    public override int GetHashCode() =>
        HashCode.Combine(Src, Tgt);

    public override string ToString() => $"{Src} --{Subst};{string.Join(", ", SideConstraints)}--> {Tgt}";
}