/-ai
Scott 1976, (3.5)–(3.6). The operator component of a pair code k is the first component of the unpairing of k.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (3.5)–(3.6).** Components of a pair code. -/
noncomputable def opNat (k : ℕ) : ℕ := (unpair k).1

end DomainTheory.DataTypesAsLattices
