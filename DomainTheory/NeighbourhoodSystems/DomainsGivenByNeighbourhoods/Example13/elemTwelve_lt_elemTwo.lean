module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
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
