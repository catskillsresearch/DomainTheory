/-ai
Scott 1976, Theorem 3.2 (ii). The numerical evaluator sends the application code of n and m to the application of its value at n to its value at m.

Unfold the application code and rewrite the successor clause of the evaluator by the identity that unpairing inverts pairing.
ai-/
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.applyNat
public import DomainTheory.DataTypesAsLattices.Enumeration.valNat
public import DomainTheory.DataTypesAsLattices.Enumeration.valNat_succ

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, Theorem 3.2 (ii).** `val(apply(n)(m)) = val n (val m)`. -/
theorem valNat_apply (n m : ℕ) :
    valNat (applyNat n m) = valNat n ⬝ valNat m := by
  rw [applyNat, valNat_succ, unpair_pair]

end DomainTheory.DataTypesAsLattices
