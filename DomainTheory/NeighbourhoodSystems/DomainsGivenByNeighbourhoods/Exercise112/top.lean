module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise112.mem_tail
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise112.tail_inter
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise112.mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise112.neighborhoodSystem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise112.ns_mem

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise112

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- The **limit element** `top`: the filter of *all* tails (Scott's single limit node). -/
def top : neighborhoodSystem.Element where
  mem X := neighborhoodSystem.mem X
  sub h := h
  master_mem := neighborhoodSystem.master_mem
  inter_mem := by
    rintro X Y ⟨n, rfl⟩ ⟨m, rfl⟩
    exact ⟨max n m, tail_inter n m⟩
  up_mem _ hY _ := hY

end DomainTheory.NeighbourhoodSystems.Exercise112
