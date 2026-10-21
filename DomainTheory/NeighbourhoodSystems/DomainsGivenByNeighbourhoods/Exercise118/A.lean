/-ai
The set A is the subset {0, 1} of the three-element set.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic

@[expose] public section

set_option linter.unusedSectionVars false

set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems

namespace triSys

/-- `A = {0,1}`. -/
def A : Set (Fin 3) := {0, 1}

end triSys

end DomainTheory.NeighbourhoodSystems
