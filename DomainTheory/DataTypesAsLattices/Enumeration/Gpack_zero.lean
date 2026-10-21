/-ai
Applying the packed combinator to the numeral 0 returns successor.

Unfold the packed sequence and apply the left-projection law for a pair sequence.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup

@[expose] public section

set_option linter.unusedSectionVars false

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

theorem Gpack_zero : funOf Gpack (ofNat 0) = sucC := by
  simp [Gpack, seq2_app_zero]

end DomainTheory.DataTypesAsLattices
