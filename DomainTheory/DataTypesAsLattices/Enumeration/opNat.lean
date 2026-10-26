module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Pomega.pair

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (3.5)–(3.6).** Components of a pair code. -/
noncomputable def opNat (k : ℕ) : ℕ := (unpair k).1

end DomainTheory.DataTypesAsLattices
