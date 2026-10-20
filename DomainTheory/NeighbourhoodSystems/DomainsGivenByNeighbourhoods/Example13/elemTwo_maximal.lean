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
