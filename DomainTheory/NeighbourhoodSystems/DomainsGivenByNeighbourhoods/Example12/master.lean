/-ai
The master neighbourhood of Example 1.2 is the set of all tokens {0, 1}.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.Token

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Example12

/-- The master neighbourhood `Δ = {0, 1}`. -/
def master : Set Token := Set.univ

end DomainTheory.NeighbourhoodSystems.Example12
