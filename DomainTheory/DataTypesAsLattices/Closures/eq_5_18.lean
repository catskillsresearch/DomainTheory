module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices











/-- **Scott 1976, (5.18).** If `a` is already a closure, then `V(a)(x) ⊆ a(x)`. -/
theorem eq_5_18 {a : Pomega} (ha : IsClosure a) (x : Pomega) :
    Vapply a x ⊆ funOf a x := by
  intro k hk
  have hx : x ⊆ funOf a x := by
    have := funOf_monotone_left ha.1 x
    rwa [Icomb_app] at this
  have haa : funOf a (funOf a x) ⊆ funOf a x := by
    simp [retract_app ha.2]
  exact hk (funOf a x) ⟨hx, haa⟩

end DomainTheory.DataTypesAsLattices
