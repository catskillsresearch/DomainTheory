/-ai
The set Cc is the subset {0, 2} of the three-element set.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic

@[expose] public section

set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems

namespace triSys

/-- `Cc = {0,2}`. -/
def Cc : Set (Fin 3) := {0, 2}

end triSys

end DomainTheory.NeighbourhoodSystems
