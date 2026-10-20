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

theorem Gpack_one : funOf Gpack (ofNat 1) =
    seq2 predC (seq2 condC (seq2 Kcomb Scomb)) := by
  simp [Gpack, seq2_app_one]

end DomainTheory.DataTypesAsLattices
