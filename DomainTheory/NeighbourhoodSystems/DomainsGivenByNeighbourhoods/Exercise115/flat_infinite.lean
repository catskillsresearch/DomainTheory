module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise115.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise115.flat_mem_singleton

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise115

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem








/-- `flat` is infinite: the atoms `↑{n}` are pairwise distinct. -/
theorem flat_infinite : Function.Injective (fun n => flat.principal (flat_mem_singleton n)) := by
  intro n m h
  have := flat.principal_injective (flat_mem_singleton n) (flat_mem_singleton m) h
  exact Set.singleton_injective this

end DomainTheory.NeighbourhoodSystems.Exercise115
