module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import Mathlib.Data.Set.Finite.Basic
import all Mathlib.Data.Set.Finite.Basic
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.powerSet
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.mem_powerSet
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.powerSet_master
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.powerSet_inter_mem
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.mem_toSet

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise220

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- The filter of a subset `S ⊆ ℕ`: the cofinite `Z` with `Zᶜ ⊆ S`. -/
def ofSet (S : Set ℕ) : powerSet.Element where
  mem Z := powerSet.mem Z ∧ Zᶜ ⊆ S
  sub h := h.1
  master_mem := ⟨powerSet.master_mem, by rw [powerSet_master, Set.compl_univ]; exact Set.empty_subset S⟩
  inter_mem := by
    rintro Z W ⟨hZ, hZS⟩ ⟨hW, hWS⟩
    refine ⟨powerSet_inter_mem hZ hW, ?_⟩
    rw [Set.compl_inter]; exact Set.union_subset hZS hWS
  up_mem := by
    rintro Z W ⟨hZ, hZS⟩ hW hZW
    exact ⟨hW, (Set.compl_subset_compl.mpr hZW).trans hZS⟩

end DomainTheory.NeighbourhoodSystems.Exercise220
