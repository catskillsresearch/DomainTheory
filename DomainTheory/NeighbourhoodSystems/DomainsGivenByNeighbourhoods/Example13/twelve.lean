module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.Token

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Example13

/-- The neighbourhood `{1, 2}`. -/
def twelve : Set Token := (insert 2 {1} : Set Token)

end DomainTheory.NeighbourhoodSystems.Example13
