using System.Diagnostics;
using System.Diagnostics.CodeAnalysis;
using System.Runtime.InteropServices.ComTypes;
using System.Security.Cryptography;
using System.Text;
using Microsoft.Z3;
using StringBreaker.Constraints;
using StringBreaker.MiscUtils;
using StringBreaker.Strings;
using StringBreaker.Strings.Tokens;

namespace StringBreaker.IntUtils;

public class Poly : MSet<StrictMonomial> {

    public bool IsZero => IsEmpty();

    public Len ConstPart => occurrences.TryGetValue([], out var c) ? c : 0;

    public Poly() { }

    public Poly(Len l) {
        StrictMonomial constMonomial = new();
        Add(constMonomial, l);
    }

    public Poly(NonTermInt v) : base(new StrictMonomial(v)) { }

    public Poly(StrictMonomial s) : base(s) { }

    public Poly(MSet<StrictMonomial> s) : base(s) { }

    public Interval GetBounds(NielsenNode node) {
        Interval res = new();
        foreach (var c in this) {
            Interval curr = c.occ * c.t.GetBounds(node);
            res = res.MergeAddition(curr);
            if (res.IsFull)
                return res;
        }
        return res;
    }

    public new Poly Clone() {
        Poly poly = new();
        foreach (var c in this) {
            poly.Add(new StrictMonomial(c.t), c.occ);
        }
        return poly;
    }

    public void Plus(Poly poly) {
        foreach (var c in poly) {
            Add(c.t, c.occ);
        }
    }

    public void Plus(Len l) {
        if (l.IsZero)
            return;
        var empty = new StrictMonomial();
        if (occurrences.TryGetValue(empty, out var c)) {
            var sum = c + l;
            if (sum.IsZero)
                occurrences.Remove(empty);
            else
                occurrences[empty] = sum;
            return;
        }
        occurrences[empty] = l;
    }

    public void Sub(Poly poly) {
        foreach (var c in poly) {
            Add(c.t, -c.occ);
        }
    }

    public void Sub(Len l) => Plus(-l);

    public Poly Negate() {
        Poly ret = new();
        foreach (var (t, occ) in this) {
            ret.Add(t.Clone(), -occ);
        }
        return ret;
    }

    public static Poly Mul(Poly p1, Poly p2) {
        Poly res = new();
        foreach (var c1 in p1) {
            foreach (var c2 in p2) {
                var r = c1.t.Clone();
                foreach (var c in c2.t) {
                    r.Add(c.t, c.occ);
                }
                res.Add(r, c1.occ * c2.occ);
            }
        }
        return res;
    }

    public Poly Apply(Subst subst) {
        Poly ret = new();
        foreach (var c in this) {
            Poly p = c.t.Apply(subst);
            p = Mul(p, new Poly(c.occ));
            ret.Plus(p);
        }
        return ret;
    }

    public Poly Apply(Interpretation subst) {
        Poly ret = new();
        foreach (var c in this) {
            Poly p = c.t.Apply(subst);
            p = Mul(p, new Poly(c.occ));
            ret.Plus(p);
        }
        return ret;
    }

    public Poly Simplify(NielsenNode node) {
        Poly ret = new();
        foreach (var m in this) {
            var p = m.t.Simplify(node);
            ret.Add(p.monomial, p.coeff * m.occ);
        }
        return ret;
    }

    public void ElimConst() => occurrences.Remove([]);

    public void CollectSymbols(HashSet<NamedStrToken> vars, HashSet<SymCharToken> sChars, HashSet<IntVar> iVars, HashSet<CharToken> alphabet) {
        foreach (var c in this) {
            c.t.CollectSymbols(vars, sChars, iVars, alphabet);
        }
    }

    public void GetPosNeg(out Poly pos, out Poly neg) {
        pos = new Poly();
        neg = new Poly();
        foreach (var m in this) {
            Debug.Assert(!m.occ.IsZero);
            Debug.Assert(!m.occ.IsInf);
            if (m.occ.IsPos)
                pos.Add(m.t.Clone(), m.occ);
            else
                neg.Add(m.t.Clone(), m.occ.Abs());
        }
    }

    public IntExpr ToExpr(NielsenContext ctx) {
        if (IsEmpty())
            return ctx.Graph.Ctx.MkInt(0);
        return (IntExpr)ctx.Graph.Ctx.MkAdd(this.Select(o => ctx.Graph.Ctx.MkMul(o.occ.ToExpr(ctx), o.t.ToExpr(ctx))).ToArray());
    }

    public bool IsConst(out Len val) {
        if (IsEmpty()) {
            val = 0;
            return true;
        }
        if (Count > 1) {
            val = 0;
            return false;
        }
        var f = this.First();
        if (f.t.IsNonEmpty()) {
            val = 0;
            return false;
        }
        val = f.occ;
        return true;
    }

    public int IsUniLinear(out NonTermInt? v, out Len val) {
        val = 0;
        v = null;
        if (IsEmpty() || Count > 2)
            return 0;
        var m1 = this.First();
        if (Count == 1) {
            // p := x
            if (m1.t.Count != 1 || (m1.occ != 1 && m1.occ != -1)) 
                return 0;
            v = m1.t.First().t;
            return m1.occ == 1 ? 1 : -1;
        }
        // p := x + c
        var m2 = this.Skip(1).First();

        if (m2.t.IsEmpty() == m1.t.IsEmpty())
            return 0;
        if (m2.t.IsEmpty())
            (m1, m2) = (m2, m1);
        // m1 is the constant
        // m2 is the variable
        if ((m2.occ != 1 && m2.occ != -1) || m2.t.Count != 1)
            return 0;
        v = m2.t.First().t;
        val = m1.occ;
        return m2.occ == 1 ? 1 : -1;
    }

    public override string ToString() {
        if (IsEmpty())
            return "0";
        StringBuilder sb = new();
        bool first = true;
        foreach (var (t, occ) in this) {
            if (!first || occ.IsNeg)
                sb.Append(occ.IsNeg ? " - " : " + ");
            first = false;
            Debug.Assert(occ != 0);
            if (t.IsEmpty())
                sb.Append(occ.Abs());
            else if (occ == 1 || occ == -1)
                sb.Append(t);
            else 
                sb.Append(occ.Abs() + " * " + t);
        }
        return sb.ToString();
    }
}