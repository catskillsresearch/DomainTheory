/-ai
The partial element at node 0 is strictly below the total element at the leaf 01.

The master neighbourhood and the left branch of the partial element both belong to the total element. The two elements are unequal because the leaf 01 belongs to the total element and is neither the master neighbourhood nor the left branch.
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


theorem elemZero_lt_elem01 : elemZero < elem01 := by
  constructor
  · intro X hx
    rcases hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · intro h
    rcases h leaf01 (Or.inr (Or.inr rfl)) with h1 | h1
    · exact leaf01_ne_master h1
    · exact leaf01_ne_left h1

end neighborhoodSystem
end DomainTheory.NeighbourhoodSystems.Example14
