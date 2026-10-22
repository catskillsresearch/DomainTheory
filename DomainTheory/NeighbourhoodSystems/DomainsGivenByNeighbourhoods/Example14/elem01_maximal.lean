/-ai
The total element at the leaf 01 is maximal: any element above it equals it.

The leaf 01 belongs to the larger element, so the recognition lemma for that leaf applies.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Example14


namespace neighborhoodSystem

open NeighborhoodSystem


theorem elem01_maximal (x : neighborhoodSystem.Element) (h : elem01 ≤ x) : x = elem01 :=
  mem_leaf01_imp x (h leaf01 (Or.inr (Or.inr rfl)))

end neighborhoodSystem
end DomainTheory.NeighbourhoodSystems.Example14
