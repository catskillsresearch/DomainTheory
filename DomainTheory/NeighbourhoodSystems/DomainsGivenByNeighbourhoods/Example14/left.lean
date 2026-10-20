module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.Token

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Example14

/-- The left subtree `{0, 00, 01} = {1, 3, 4}`. -/
def left : Set Token := {1, 3, 4}

end DomainTheory.NeighbourhoodSystems.Example14
