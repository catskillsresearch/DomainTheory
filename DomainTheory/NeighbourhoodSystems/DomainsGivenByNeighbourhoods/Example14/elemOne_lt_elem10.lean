module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Example14













































namespace neighborhoodSystem

open NeighborhoodSystem
















theorem elemOne_lt_elem10 : elemOne < elem10 := by
  constructor
  · intro X hx
    rcases hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · intro h
    rcases h leaf10 (Or.inr (Or.inr rfl)) with h1 | h1
    · exact leaf10_ne_master h1
    · exact leaf10_ne_right h1

end neighborhoodSystem
end DomainTheory.NeighbourhoodSystems.Example14
