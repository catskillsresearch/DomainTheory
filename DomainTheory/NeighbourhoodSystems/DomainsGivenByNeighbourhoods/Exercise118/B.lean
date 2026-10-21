/-ai
The set B is the subset {1, 2} of the three-element set.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic

@[expose] public section

set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems

namespace triSys

/-- `B = {1,2}`. -/
def B : Set (Fin 3) := {1, 2}

end triSys

end DomainTheory.NeighbourhoodSystems
