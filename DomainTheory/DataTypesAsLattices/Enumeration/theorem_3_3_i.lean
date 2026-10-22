
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.secondRecOperator_app
public import DomainTheory.DataTypesAsLattices.Enumeration.valNat_secondRecOperatorCode

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, Theorem 3.3 (i).** -/
theorem theorem_3_3_i (n : ℕ) :
    valNat (secondRecV n) = secondRecVal (valNat n) := by
  rw [secondRecV, valNat_apply, valNat_secondRecOperatorCode,
    secondRecOperator_app]

end DomainTheory.DataTypesAsLattices
