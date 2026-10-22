/-ai
The master neighbourhood of Example 1.4 is the whole set of tokens.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.Token

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example14

/-- The master neighbourhood `Δ` (the whole tree). -/
def master : Set Token := Set.univ

end DomainTheory.NeighbourhoodSystems.Example14
