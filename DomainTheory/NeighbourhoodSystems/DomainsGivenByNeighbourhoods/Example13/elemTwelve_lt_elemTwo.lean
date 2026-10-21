/-ai
The intermediate element of Example 1.3 is strictly below the total element.

A neighbourhood of the intermediate element is the master or {1, 2}, both of which belong to the total element. The reverse inequality would put {2} in the intermediate filter, so {2} would be the master or equal to {1, 2}.
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


theorem elemTwelve_lt_elemTwo : elemTwelve < elemTwo := by
  constructor
  · intro X hx
    rcases hx with rfl | hX12
    · exact Or.inl rfl
    · exact Or.inr (Or.inl hX12)
  · intro h
    exfalso
    have ht := h two (Or.inr (Or.inr rfl))
    rcases ht with h1 | h2
    · exact absurd h1 two_ne_master
    · exact two_ne_twelve h2

end neighborhoodSystem
end DomainTheory.NeighbourhoodSystems.Example13
