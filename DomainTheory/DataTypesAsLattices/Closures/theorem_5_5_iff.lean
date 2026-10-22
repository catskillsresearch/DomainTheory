/-ai
A set is a closure if and only if it is a fixed point of the universe combinator.

If the set is a closure, applying the universe combinator yields the graph of its value operator, that graph equals the graph of the set because the operator agrees with the closure on values, and the graph equals the set because the set is a retract. Conversely, a fixed point of the universe combinator is the graph of its value operator, so application of the set is that operator by the beta law. Pairs from the identity combinator remain in the graph because every finite set is contained in the value of the operator on it. The value operator is idempotent and agrees with application of the set, so the graph of the operator is the graph of the double application, and the set is a retract.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_16
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_17
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_18_eq
public import DomainTheory.DataTypesAsLattices.Closures.Vapply_right_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Closures.Vcomb_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, (5.18).** `a = V(a)` iff `a` is a closure. -/
theorem theorem_5_5_iff (a : Pomega) :
    Closure a ↔ funOf Vcomb a = a := by
  constructor
  · intro ha
    rw [Vcomb_app]
    have : graph (fun x => Vapply a x) = graph (funOf a) :=
      graph_ext fun x => eq_5_18_eq ha x
    exact this.trans (retract_isGraph ha.out.2)
  · intro h
    have ha : a = graph (fun x => Vapply a x) :=
      h.symm.trans (Vcomb_app a)
    have happ : ∀ x, funOf a x = Vapply a x := by
      intro x
      conv_lhs => rw [ha]
      exact beta (Vapply_right_isScottContinuous a) x
    constructor
    constructor
    · intro p hp
      rcases hp with ⟨n, m, rfl, hm⟩
      have : pair n m ∈ graph (fun x => Vapply a x) :=
        ⟨n, m, rfl, eq_5_16 a (e n) hm⟩
      rwa [← ha] at this
    · have : graph (fun x => Vapply a x) =
          graph (fun x => funOf a (funOf a x)) :=
        graph_ext fun x =>
          calc Vapply a x
              = Vapply a (Vapply a x) := (eq_5_17 a x).symm
            _ = funOf a (Vapply a x) := (happ (Vapply a x)).symm
            _ = funOf a (funOf a x) := by rw [← happ x]
      exact ⟨ha.trans this⟩

end DomainTheory.DataTypesAsLattices
