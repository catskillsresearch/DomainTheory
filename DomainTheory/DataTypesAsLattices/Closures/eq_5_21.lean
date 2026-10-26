module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Lambda.xi_star
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Closures.Vcomb
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_1
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_18
public import DomainTheory.DataTypesAsLattices.Closures.Vcomb_more
@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, (5.21).** `a ⊆ V(a)`. -/
theorem eq_5_21 (a : Pomega) : a ⊆ funOf Vcomb a := by
  rw [Vcomb.app]
  exact (eq_5_1 a).trans (xi_star fun x => eq_5_18.rev a x)

end DomainTheory.DataTypesAsLattices
