/-ai
The bottom element of Example 1.2 is strictly below the total element determined by {0}.

Every neighbourhood of the bottom element is the master, which belongs to the larger element. The reverse inequality would put {0} in the bottom filter, forcing {0} to be the master.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Example12























namespace neighborhoodSystem

open NeighborhoodSystem






/-- The bottom filter is the only partial element: it is strictly below both total elements. -/
theorem bot_lt_elemZero : bot < elemZero := by
  constructor
  · intro X hx; exact Or.inl hx
  · intro h
    have : bot.mem zero := h zero (Or.inr rfl)
    have hm : zero = master := this
    exact zero_ne_master hm

end neighborhoodSystem
end DomainTheory.NeighbourhoodSystems.Example12
