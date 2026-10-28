
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Enumeration.applyNat
public import DomainTheory.DataTypesAsLattices.Enumeration.secondRecOperatorCode

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

noncomputable def secondRecV (n : ℕ) : ℕ :=
  applyNat secondRecOperatorCode n

end DomainTheory.DataTypesAsLattices
