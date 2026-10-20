module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Data.Set.Finite.Basic
import all Mathlib.Data.Set.Finite.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.cofiniteSystem_mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.ofExcluded
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.mem_ofExcluded
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.toExcluded
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.mem_toExcluded

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Cofinite

open NeighborhoodSystem

theorem toExcluded_ofExcluded (E : Set ℕ) : toExcluded (ofExcluded E) = E := by
  ext n
  rw [mem_toExcluded, mem_ofExcluded]
  simp [compl_compl, Set.finite_singleton, Set.singleton_subset_iff]

end Cofinite

end DomainTheory.NeighbourhoodSystems
