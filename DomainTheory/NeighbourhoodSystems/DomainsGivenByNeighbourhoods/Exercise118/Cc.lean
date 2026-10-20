module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic

@[expose] public section

set_option linter.unusedSectionVars false

set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems

namespace triSys

/-- `Cc = {0,2}`. -/
def Cc : Set (Fin 3) := {0, 2}

end triSys

end DomainTheory.NeighbourhoodSystems
