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


/-- **Exercise 6.29 — `⊗` does not generalize.** Over an infinite index, the smash product has only
its basepoint: an all-coordinates-proper cylinder has support `Set.univ`, which cannot be finite. -/
theorem iotimes_only_master [Infinite ι] (D : ∀ i, NeighborhoodSystem (α i)) :
    ∀ W, (iotimes D).mem W → W = (iotimes D).master := by
  rintro W (rfl | ⟨X, _, hXne, ⟨l, hl⟩, rfl⟩)
  · rfl
  · -- Every coordinate is proper, so the finite support list `l` would have to contain *all* of `ι`,
    -- impossible for an infinite index. This is a cardinality argument: Prop-level and unavoidably
    -- classical (Mathlib's `Set.Finite`/`Fintype` API is built on `Classical.choice`).
    refine absurd ((List.finite_toSet l).subset (fun i _ => ?_)) Set.infinite_univ
    exact not_not.mp fun hni => hXne i (hl i hni)

end Exercise629
end DomainTheory.NeighbourhoodSystems
