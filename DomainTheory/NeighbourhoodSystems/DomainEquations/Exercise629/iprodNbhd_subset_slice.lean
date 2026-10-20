module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import Mathlib.Data.Set.Finite.Basic
import all Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Finset.Basic
import all Mathlib.Data.Finset.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.iprodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.mem_iprodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.iprodNbhd_subset_iff
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.updTuple_apply_self
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.updTuple_apply_ne
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.slice
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.slice_eq

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

section IndexedProduct

variable [Nonempty ι]


section Iso

variable [DecidableEq ι]

omit [Nonempty ι] in
/-- A cylinder is contained in each of its own slices. -/
theorem iprodNbhd_subset_slice {X : ∀ i, Set (α i)} (hX : ∀ i, (D i).mem (X i)) (i : ι) :
    iprodNbhd X ⊆ slice D i (X i) := by
  rw [slice_eq, iprodNbhd_subset_iff]
  intro j
  by_cases h : j = i
  · subst h; rw [updTuple_apply_self]
  · rw [updTuple_apply_ne (X i) h]; exact (D j).sub_master (hX j)

end Iso

end IndexedProduct

end Exercise629

end DomainTheory.NeighbourhoodSystems
