module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Pomega.pair

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

noncomputable def opNat (k : ℕ) : ℕ := (unpair k).1

end DomainTheory.DataTypesAsLattices
