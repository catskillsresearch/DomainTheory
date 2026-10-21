/-ai
Scott 1976, before Theorem 3.5. The code fin j is the primitive recursive bit scan finAux j (j + 1). It is a uniform code for the finite set e_j, and the only fixed choice it makes is a code for binary union.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.finAux

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, before Theorem 3.5.** A uniform primitive-recursive code
for `e j`; unlike the former definition, this makes only one fixed choice,
namely a code for binary union. -/
noncomputable def fin (j : ℕ) : ℕ := finAux j (j + 1)

end DomainTheory.DataTypesAsLattices
