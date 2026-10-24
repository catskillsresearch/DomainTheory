module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic.Set
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.ApproximableMap
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.sSupDirected
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.toElementMap
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.idMap
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.comp
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.ofIso
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.ext
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.mem_toElementMap
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.idMap_rel
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.comp_rel
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.toElementMap_idMap

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

namespace NeighborhoodSystem


/-- Each member of a directed family approximates the directed union. -/
theorem le_sSupDirected (V : NeighborhoodSystem α) (S : Set V.Element) (hne : S.Nonempty)
    (hdir : ∀ a ∈ S, ∀ b ∈ S, ∃ c ∈ S, a ≤ c ∧ b ≤ c) {a : V.Element} (ha : a ∈ S) :
    a ≤ V.sSupDirected S hne hdir :=
  fun _ hZ => ⟨a, ha, hZ⟩

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
