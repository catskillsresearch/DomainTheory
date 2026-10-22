/-ai
The bottom element of Example 1.2 is strictly below the total element determined by {1}.

Every neighbourhood of the bottom element is the master, which belongs to the larger element. The reverse inequality would put {1} in the bottom filter, forcing {1} to be the master.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Example12


namespace neighborhoodSystem

open NeighborhoodSystem


theorem bot_lt_elemOne : bot < elemOne := by
  constructor
  · intro X hx; exact Or.inl hx
  · intro h
    have : bot.mem one := h one (Or.inr rfl)
    have hm : one = master := this
    exact one_ne_master hm

end neighborhoodSystem
end DomainTheory.NeighbourhoodSystems.Example12
