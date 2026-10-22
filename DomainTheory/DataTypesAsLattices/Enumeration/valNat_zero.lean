/-ai
Scott 1976, Theorem 3.2 (i). The numerical evaluator sends zero to the G combinator.

Unfold the evaluator and apply the computation rule for strong recursion.
ai-/
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.valNat

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, Theorem 3.2 (i).** `val(0) = G`. -/
theorem valNat_zero : valNat 0 = Gcomb := by
  unfold valNat
  rw [Nat.strongRec]

end DomainTheory.DataTypesAsLattices
