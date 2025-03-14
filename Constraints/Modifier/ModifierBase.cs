using System.Diagnostics;
using StringBreaker.Constraints.ConstraintElement;
using StringBreaker.Tokens;

namespace StringBreaker.Constraints.Modifier;

public abstract class ModifierBase : IComparable<ModifierBase> {

    // This should be unique!! [whether left or right reduce is saved within the modifier]
    static readonly Dictionary<Type, int> TypeOrder = [];

    static ModifierBase() {
        TypeOrder.Add(typeof(DetModifier), TypeOrder.Count);
        // u = "" || n = 0
        TypeOrder.Add(typeof(PowerEpsilonModifier), TypeOrder.Count);
        // x := ax || x := ""
        TypeOrder.Add(typeof(ConstNielsenModifier), TypeOrder.Count);
        // \/ x := u^n postfix(u); u const
        TypeOrder.Add(typeof(GPowerIntrModifier), TypeOrder.Count);
        // \/ x := u^n postfix(u) || \/ y := v^m postfix(v); u, v const
        TypeOrder.Add(typeof(GPowerGPowerIntrModifier), TypeOrder.Count);
        // x := "" || (y := "" && |x| > 0) || (x := y && |x| > 0) || (x := yx && |x| > 0 && |y| > 0) ||( y := xy && |x| > 0 && |y| > 0)
        TypeOrder.Add(typeof(VarNielsenModifier), TypeOrder.Count);
        // \/ x := u^n postfix(u); u const || y := xy
        TypeOrder.Add(typeof(GPowerIntrConstNielsen), TypeOrder.Count);
        // n <= m || n > m
        TypeOrder.Add(typeof(NumCmpModifier), TypeOrder.Count);
        // n := 0 || n > 0
        TypeOrder.Add(typeof(NumUnwindingModifier), TypeOrder.Count);
        // \/ x := u^n postfix(u); u not const
        TypeOrder.Add(typeof(PowerIntrModifier), TypeOrder.Count);
        // \/ x := u^n postfix(u); u not const \/ y := xy
        TypeOrder.Add(typeof(PowerIntrConstNielsen), TypeOrder.Count);
        // \/ x := u^n postfix(u); u not const || \/ y := v^m postfix(v); u, v not const
        TypeOrder.Add(typeof(PowerPowerIntrModifier), TypeOrder.Count);
    }

    protected ModifierBase() => 
        Debug.Assert(TypeOrder.ContainsKey(GetType()));

    public abstract void Apply(NielsenNode node);
    protected abstract int CompareToInternal(ModifierBase otherM);

    public int CompareTo(ModifierBase? other) {
        if (other is null)
            return 1;
        var c1 = this is CombinedModifier cm1 ? cm1.Modifier : [this];
        var c2 = other is CombinedModifier cm2 ? cm2.Modifier : [other];

        int highest1 = 0, highest2 = 0;
        ModifierBase d1 = this, d2 = other;
        foreach (var c in c1) {
            int v = TypeOrder[c.GetType()];
            if (v <= highest1) 
                continue;
            highest1 = v;
            d1 = c;
        }
        foreach (var c in c2) {
            int v = TypeOrder[c.GetType()];
            if (v <= highest2) 
                continue;
            highest2 = v;
            d2 = c;
        }
        if (highest1 != highest2)
            return highest1.CompareTo(highest2);
        Debug.Assert(d1.GetType() == d2.GetType());
        return d1.CompareToInternal(d2);
    }

    public abstract override string ToString();
}