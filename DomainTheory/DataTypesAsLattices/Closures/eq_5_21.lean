module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_1
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_18_rev
public import DomainTheory.DataTypesAsLattices.Closures.Vcomb_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, (5.21).** `a ⊆ V(a)`. -/
theorem eq_5_21 (a : Pomega) : a ⊆ funOf Vcomb a := by
  rw [Vcomb_app]
  exact (eq_5_1 a).trans (xi_star fun x => eq_5_18_rev a x)

end DomainTheory.DataTypesAsLattices
