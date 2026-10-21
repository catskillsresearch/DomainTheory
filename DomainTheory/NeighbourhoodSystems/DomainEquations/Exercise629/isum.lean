/-ai
The indexed separated sum of a family of neighbourhood systems, assuming every neighbourhood is nonempty, is the neighbourhood system on optional dependent pairs whose neighbourhoods are the sum master and the tagged copies of the neighbourhoods of the summands, and whose own master is the sum master.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import Mathlib.Data.Set.Finite.Basic
import all Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Finset.Basic
import all Mathlib.Data.Finset.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.mem_iprodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.updTuple_apply_self
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.injI
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.none_not_mem_injI
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.some_mem_injI
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.index_of_some_mem_injI
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.injI_subset_iff
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.injI_inter_same
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.sumMasterI
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.none_mem_sumMasterI
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.injI_subset_sumMasterI

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

/-- **Exercise 6.29 — the indexed separated sum `∑_i D_i`.** -/
def isum (D : ∀ i, NeighborhoodSystem (α i))
    (hne : ∀ i, ∀ X : Set (α i), (D i).mem X → X.Nonempty) :
    NeighborhoodSystem (Option (Σ i, α i)) where
  mem W := W = sumMasterI D ∨ ∃ i, ∃ X : Set (α i), (D i).mem X ∧ W = injI i X
  master := sumMasterI D
  master_nonempty := ⟨none, none_mem_sumMasterI⟩
  master_mem := Or.inl rfl
  sub_master := by
    rintro W (rfl | ⟨i, X, hX, rfl⟩)
    · exact subset_rfl
    · exact injI_subset_sumMasterI hX
  inter_mem := by
    rintro W W' Z hW hW' hZ hsub
    rcases hW with rfl | ⟨i, X, hX, rfl⟩
    · have hsub' : W' ⊆ sumMasterI D := by
        rcases hW' with rfl | ⟨j, Y, hY, rfl⟩
        · exact subset_rfl
        · exact injI_subset_sumMasterI hY
      rw [Set.inter_eq_right.mpr hsub']; exact hW'
    · rcases hW' with rfl | ⟨j, Y, hY, rfl⟩
      · rw [Set.inter_eq_left.mpr (injI_subset_sumMasterI hX)]
        exact Or.inr ⟨i, X, hX, rfl⟩
      · -- both proper: the consistency witness `Z` forces `i = j` constructively.
        rcases hZ with rfl | ⟨k, Wk, hWk, rfl⟩
        · exact absurd (hsub none_mem_sumMasterI).1 none_not_mem_injI
        · obtain ⟨w, hw⟩ := hne k Wk hWk
          have hmemZ := hsub (some_mem_injI.mpr hw)
          obtain rfl := index_of_some_mem_injI hmemZ.1
          obtain rfl := index_of_some_mem_injI hmemZ.2
          rw [injI_inter_same] at hsub ⊢
          exact Or.inr ⟨k, X ∩ Y, (D k).inter_mem hX hY hWk (injI_subset_iff.mp hsub), rfl⟩

end Exercise629

end DomainTheory.NeighbourhoodSystems
