/-ai
The bottom element of Example 1.3 is strictly below the intermediate element.

A neighbourhood of the bottom element is the master, which belongs to the intermediate element. The reverse inequality would put {1, 2} in the bottom filter, forcing {1, 2} to equal the master.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Example13






















namespace neighborhoodSystem

open NeighborhoodSystem







theorem bot_lt_elemTwelve : bot < elemTwelve := by
  constructor
  · intro X hx
    rw [hx]
    exact Or.inl rfl
  · intro h
    have : bot.mem twelve := h twelve (Or.inr rfl)
    exact twelve_ne_master this

end neighborhoodSystem
end DomainTheory.NeighbourhoodSystems.Example13
