/-ai
The bottom element is strictly below the partial element at node 0.

Every neighbourhood of the bottom element is the master neighbourhood, which belongs to the partial element. The two elements are unequal because the left branch belongs to the partial element and is distinct from the master neighbourhood.
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


theorem bot_lt_elemZero : bot < elemZero := by
  constructor
  · intro X hx; rw [hx]; exact Or.inl rfl
  · intro h
    exact left_ne_master (h left (Or.inr rfl))

end neighborhoodSystem
end DomainTheory.NeighbourhoodSystems.Example14
