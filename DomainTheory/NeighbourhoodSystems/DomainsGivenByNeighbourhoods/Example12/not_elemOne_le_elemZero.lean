module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Example12























namespace neighborhoodSystem

open NeighborhoodSystem







theorem not_elemOne_le_elemZero : ¬ elemOne ≤ elemZero := by
  intro h
  rcases h one (Or.inr rfl) with h' | h'
  · exact one_ne_master h'
  · exact zero_ne_one h'.symm

end neighborhoodSystem
end DomainTheory.NeighbourhoodSystems.Example12
