module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Example14


namespace neighborhoodSystem

open NeighborhoodSystem


theorem elemOne_lt_elem11 : elemOne < elem11 := by
  constructor
  · intro X hx
    rcases hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · intro h
    rcases h leaf11 (Or.inr (Or.inr rfl)) with h1 | h1
    · exact leaf11_ne_master h1
    · exact leaf11_ne_right h1

end neighborhoodSystem
end DomainTheory.NeighbourhoodSystems.Example14
