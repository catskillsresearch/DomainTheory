module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂

theorem fin2_zero_subset_zero_one : ({0} : Set (Fin 2)) ⊆ ({0, 1} : Set (Fin 2)) := by
  intro x hx; simp only [Set.mem_singleton_iff] at hx; subst hx; simp

end DomainTheory.NeighbourhoodSystems
