/-ai
The partial element at node 1 is strictly below the total element at the leaf 10.

The master neighbourhood and the right branch of the partial element both belong to the total element. The two elements are unequal because the leaf 10 belongs to the total element and is neither the master neighbourhood nor the right branch.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Example14


namespace neighborhoodSystem

open NeighborhoodSystem


theorem elemOne_lt_elem10 : elemOne < elem10 := by
  constructor
  · intro X hx
    rcases hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · intro h
    rcases h leaf10 (Or.inr (Or.inr rfl)) with h1 | h1
    · exact leaf10_ne_master h1
    · exact leaf10_ne_right h1

end neighborhoodSystem
end DomainTheory.NeighbourhoodSystems.Example14
