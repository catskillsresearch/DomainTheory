/-ai
The total element at the leaf 10 is maximal: any element above it equals it.

The leaf 10 belongs to the larger element, so the recognition lemma for that leaf applies.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Example14


namespace neighborhoodSystem

open NeighborhoodSystem


theorem elem10_maximal (x : neighborhoodSystem.Element) (h : elem10 ≤ x) : x = elem10 :=
  mem_leaf10_imp x (h leaf10 (Or.inr (Or.inr rfl)))

end neighborhoodSystem
end DomainTheory.NeighbourhoodSystems.Example14
