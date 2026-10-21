/-ai
The bottom element is strictly below the partial element at node 1.

Every neighbourhood of the bottom element is the master neighbourhood, which belongs to the partial element. The two elements are unequal because the right branch belongs to the partial element and is distinct from the master neighbourhood.
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


theorem bot_lt_elemOne : bot < elemOne := by
  constructor
  · intro X hx; rw [hx]; exact Or.inl rfl
  · intro h
    exact right_ne_master (h right (Or.inr rfl))

end neighborhoodSystem
end DomainTheory.NeighbourhoodSystems.Example14
