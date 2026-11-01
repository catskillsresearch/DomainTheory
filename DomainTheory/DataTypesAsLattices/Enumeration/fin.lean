module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Enumeration.finAux
public import DomainTheory.DataTypesAsLattices.Pomega.eDense

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

noncomputable def fin (j : ℕ) : ℕ := finAux j (j + 1)

end DomainTheory.DataTypesAsLattices
