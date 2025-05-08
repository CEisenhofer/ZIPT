using System.Diagnostics;
using System.Text;
using StringBreaker.MiscUtils;

namespace StringBreaker.IntUtils;

public class Poly<L, T> : MSet<StrictMonomial, L> where L : IArith<L>, new() where T : Poly<L, T>, new() {

    public bool IsZero => IsEmpty();

    public L ConstPart => occurrences.TryGetValue([], out var c) ? c : new L();

    public IEnumerable<(StrictMonomial t, L occ)> NonConst =>
        this.Where(c => !c.t.IsEmpty());

    public Poly() { }

    public Poly(L l) {
        StrictMonomial constMonomial = new();
        Add(constMonomial, l);
    }

    public Poly(NonTermInt v) : base(new StrictMonomial(v)) { }

    public Poly(StrictMonomial s) : base(s) { }

    public Poly(MSet<StrictMonomial, L> s) : base(s) { }

    public void Plus(T poly) {
        foreach (var c in poly) {
            Add(c.t, c.occ);
        }
    }

    public void Plus(L l) => Plus(new StrictMonomial(), l);

    public void Plus(StrictMonomial m, L l) {
        if (l.IsZero)
            return;
        if (occurrences.TryGetValue(m, out var c)) {
            var sum = c.Add(l);
            if (sum.IsZero)
                occurrences.Remove(m);
            else
                occurrences[m] = sum;
            return;
        }
        occurrences[m] = l;
    }

    public void Sub(T poly) {
        foreach (var c in poly) {
            Add(c.t, c.occ.Negate());
        }
    }

    public void Sub(L l) => Plus(l.Negate());
    public void Sub(L l, StrictMonomial m) => Plus(m, l.Negate());

    public T Negate() {
        T ret = new();
        foreach (var (t, occ) in this) {
            ret.Add(t.Clone(), occ.Negate());
        }
        return ret;
    }

    public static T Mul(T p1, T p2) {
        T res = new();
        foreach (var c1 in p1) {
            foreach (var c2 in p2) {
                var r = c1.t.Clone();
                foreach (var c in c2.t) {
                    r.Add(c.t, c.occ);
                }
                res.Add(r, c1.occ.Mul(c2.occ));
            }
        }
        return res;
    }

    public T Div(L n) {
        Debug.Assert(!n.IsZero);
        T ret = new();
        foreach (var c in this) {
            Debug.Assert(!c.occ.IsZero);
            var r = c.occ.Div(n);
            Debug.Assert(!r.IsZero);
            var t = c.t.Clone();
            ret.Add(t, r);
        }
        return ret;
    }

    public void ElimConst() => occurrences.Remove([]);

    public void GetPosNeg(out T pos, out T neg) {
        pos = new T();
        neg = new T();
        foreach (var m in this) {
            Debug.Assert(!m.occ.IsZero);
            if (m.occ.IsPos)
                pos.Add(m.t.Clone(), m.occ);
            else
                neg.Add(m.t.Clone(), m.occ.Abs());
        }
    }

    public bool IsConst(out L val) {
        if (IsEmpty()) {
            val = new L();
            return true;
        }
        if (Count > 1) {
            val = new L();
            return false;
        }
        var f = this.First();
        if (f.t.IsNonEmpty()) {
            val = new L();
            return false;
        }
        val = f.occ;
        return true;
    }

    public int IsUniLinear(out NonTermInt? v, out L val) {
        val = new L();
        v = null;
        if (IsEmpty() || Count > 2)
            return 0;
        var m1 = this.First();
        if (Count == 1) {
            // p := x
            if (m1.t.Count != 1 || (!m1.occ.IsOne && !m1.occ.IsMinusOne)) 
                return 0;
            v = m1.t.First().t;
            return m1.occ.IsOne ? 1 : -1;
        }
        // p := x + c
        var m2 = this.Skip(1).First();

        if (m2.t.IsEmpty() == m1.t.IsEmpty())
            return 0;
        if (m2.t.IsEmpty())
            (m1, m2) = (m2, m1);
        // m1 is the constant
        // m2 is the variable
        if ((!m2.occ.IsOne && !m2.occ.IsMinusOne) || m2.t.Count != 1)
            return 0;
        v = m2.t.First().t;
        val = m1.occ;
        return m2.occ.IsOne ? 1 : -1;
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
            Debug.Assert(!occ.IsZero);
            if (t.IsEmpty())
                sb.Append(occ.Abs());
            else if (occ.IsOne || occ.IsMinusOne)
                sb.Append(t);
            else 
                sb.Append(occ.Abs() + " * " + t);
        }
        return sb.ToString();
    }
}