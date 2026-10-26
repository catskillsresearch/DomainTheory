module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Enumeration.finAux
public import DomainTheory.DataTypesAsLattices.Pomega.e

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, before Theorem 3.5.** A uniform primitive-recursive code
for `e j`; unlike the former definition, this makes only one fixed choice,
namely a code for binary union. -/
noncomputable def fin (j : ℕ) : ℕ := finAux j (j + 1)

end DomainTheory.DataTypesAsLattices
