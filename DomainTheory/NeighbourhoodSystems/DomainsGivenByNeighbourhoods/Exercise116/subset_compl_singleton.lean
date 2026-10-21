/-ai
If a natural number lies outside a set, that set is contained in the complement of the singleton of that number.

A point of the set cannot equal that number, or the number would belong to the set.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Data.Set.Finite.Basic
import all Mathlib.Data.Set.Finite.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.cofiniteSystem_mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.mem_ofExcluded
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.mem_toExcluded

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Cofinite

open NeighborhoodSystem

/-- For `n ∉ Y`, the neighbourhood `Y` is contained in `{n}ᶜ`. -/
theorem subset_compl_singleton {Y : Set ℕ} {n : ℕ} (hn : n ∈ Yᶜ) : Y ⊆ ({n} : Set ℕ)ᶜ := by
  intro m hm
  rw [Set.mem_compl_iff, Set.mem_singleton_iff]
  rintro rfl
  exact hn hm

end Cofinite

end DomainTheory.NeighbourhoodSystems
