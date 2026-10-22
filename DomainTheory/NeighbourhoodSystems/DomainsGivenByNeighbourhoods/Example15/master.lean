/-ai
The master neighbourhood of Example 1.5 is the set of all four tokens.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example15.Token

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example15

open NeighborhoodSystem

/-- The master neighbourhood `Δ = {0, 1, 2, 3}`. -/
def master : Set Token := Set.univ

end DomainTheory.NeighbourhoodSystems.Example15
