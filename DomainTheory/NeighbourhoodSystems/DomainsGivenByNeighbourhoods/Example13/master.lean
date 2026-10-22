/-ai
The master neighbourhood of Example 1.3 is the set of all tokens {0, 1, 2}.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.Token

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example13

/-- The master neighbourhood `Δ = {0, 1, 2}`. -/
def master : Set Token := Set.univ

end DomainTheory.NeighbourhoodSystems.Example13
