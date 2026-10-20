module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices











/-- **Scott 1976, (5.16).** `x ⊆ V(a)(x)`. -/
theorem eq_5_16 (a x : Pomega) : x ⊆ Vapply a x := by
  intro k hk y hy
  exact hy.1 hk

end DomainTheory.DataTypesAsLattices
