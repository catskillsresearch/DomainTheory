module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.cofiniteSystem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.cofiniteSystem_mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.mem_ofExcluded
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.mem_toExcluded

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Cofinite

open NeighborhoodSystem

/-- Each `{n}ᶜ` is a neighbourhood (its complement `{n}` is finite). -/
theorem mem_compl_singleton (n : ℕ) : cofiniteSystem.mem (({n} : Set ℕ)ᶜ) := by
  rw [cofiniteSystem_mem, compl_compl]
  exact Set.finite_singleton n

end Cofinite

end DomainTheory.NeighbourhoodSystems
