module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, (5.1).** `u ⊆ λx. u(x)`. -/
theorem eq_5_1 (u : Pomega) : u ⊆ graph (fun x => funOf u x) :=
  theorem_1_2_ii u

end DomainTheory.DataTypesAsLattices
