module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Finset.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.iprodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.FinSupp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.iprod
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.updTuple
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.slice
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.proj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.fromPi
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.restrictTo
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.iprodEquiv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.injI
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.sumMasterI
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.isum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.ioplus
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.iotimes
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.mem_iprodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.iprodNbhd_inter
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.iprodNbhd_subset_iff
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.iprodNbhd_injective
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.inter
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.updTuple_apply_self
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.updTuple_apply_ne
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.slice_eq
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.iprod_mem_slice
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.iprod_mem_slice_inv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.slice_inter
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.slice_subset
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.iprodNbhd_subset_slice
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.fromPi_mem_slice
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.iprodNbhd_restrictTo_cons
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.z_mem_iprodNbhd_restrictTo
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.z_mem_of_slices
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.fromPi_toPi
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.proj_fromPi
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.none_not_mem_injI
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.some_mem_injI
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.index_of_some_mem_injI
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.injI_subset_iff
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.injI_inter_same
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.none_mem_sumMasterI
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.injI_subset_sumMasterI

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}


variable {D : ∀ i, NeighborhoodSystem (α i)}


/-- **Exercise 6.29 — a sum element reaches at most one summand.** -/
theorem isum_summand_unique {hne : ∀ i, ∀ X : Set (α i), (D i).mem X → X.Nonempty}
    (z : (isum D hne).Element) {i j : ι} {X : Set (α i)} {Y : Set (α j)}
    (hX : z.mem (injI i X)) (hY : z.mem (injI j Y)) : i = j := by
  -- The filter element `z` contains the consistent intersection; its representative carries a
  -- token whose index is forced to be both `i` and `j` — no excluded middle on `i = j`.
  have hz := z.inter_mem hX hY
  rcases z.sub hz with h0 | ⟨k, W, hWmem, hWeq⟩
  · rw [Set.ext_iff] at h0
    exact absurd ((h0 none).mpr none_mem_sumMasterI).1 none_not_mem_injI
  · obtain ⟨w, hw⟩ := hne k W hWmem
    rw [Set.ext_iff] at hWeq
    have hmem := (hWeq (some ⟨k, w⟩)).mpr (some_mem_injI.mpr hw)
    obtain rfl := index_of_some_mem_injI hmem.1
    obtain rfl := index_of_some_mem_injI hmem.2
    rfl

end Exercise629
end DomainTheory.NeighbourhoodSystems
