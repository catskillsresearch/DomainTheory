/-ai
The total element of Example 1.3 is maximal: any element above it equals it.

The classification makes that element the bottom element, the intermediate element, or the total element. The bottom element would then contain {1, 2}, forcing {1, 2} to be the master. The intermediate element would then contain {2}, forcing {2} to be the master or equal to {1, 2}.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.element_classification

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Example13


namespace neighborhoodSystem

open NeighborhoodSystem


theorem elemTwo_maximal (x : neighborhoodSystem.Element) (h : elemTwo ≤ x) : x = elemTwo := by
  rcases element_classification x with rfl | rfl | rfl
  · exfalso
    have : bot.mem twelve := h twelve (Or.inr (Or.inl rfl))
    exact twelve_ne_master this
  · exfalso
    have ht := h two (Or.inr (Or.inr rfl))
    rcases ht with h1 | h2
    · exact absurd h1 two_ne_master
    · exact two_ne_twelve h2
  · rfl

end neighborhoodSystem
end DomainTheory.NeighbourhoodSystems.Example13
