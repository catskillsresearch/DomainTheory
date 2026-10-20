module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.Token

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Example13

/-- The master neighbourhood `Δ = {0, 1, 2}`. -/
def master : Set Token := Set.univ

end DomainTheory.NeighbourhoodSystems.Example13
