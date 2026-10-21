/-ai
The leaf 10 is the singleton consisting of the token 5.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.Token

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Example14

/-- The leaf `{10} = {5}`. -/
def leaf10 : Set Token := {5}

end DomainTheory.NeighbourhoodSystems.Example14
