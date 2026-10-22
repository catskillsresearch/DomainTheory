module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise118.A
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise118.B
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise118.Cc

@[expose] public section

set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems

namespace triSys

/-- The triple `A, B, Cc` as a finite sequence. -/
def triple : ℕ → Set (Fin 3) := fun i => if i = 0 then A else if i = 1 then B else Cc

end triSys

end DomainTheory.NeighbourhoodSystems
