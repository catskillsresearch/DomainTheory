module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Example14


namespace neighborhoodSystem

open NeighborhoodSystem


theorem elem11_maximal (x : neighborhoodSystem.Element) (h : elem11 ≤ x) : x = elem11 :=
  mem_leaf11_imp x (h leaf11 (Or.inr (Or.inr rfl)))

end neighborhoodSystem
end DomainTheory.NeighbourhoodSystems.Example14
