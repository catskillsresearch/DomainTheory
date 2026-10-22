module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Finset.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.mem_iprodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.iprodNbhd_subset_iff
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.updTuple_apply_self
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.updTuple_apply_ne
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.slice
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.slice_eq

@[expose] public section

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
/-- Slices are monotone in their data. -/
theorem slice_subset (i : ι) {U U' : Set (α i)} (hUU' : U ⊆ U') : slice D i U ⊆ slice D i U' := by
  rw [slice_eq, slice_eq, iprodNbhd_subset_iff]
  intro j
  by_cases h : j = i
  · subst h; rw [updTuple_apply_self, updTuple_apply_self]; exact hUU'
  · rw [updTuple_apply_ne U h, updTuple_apply_ne U' h]

end Iso

end IndexedProduct

end Exercise629

end DomainTheory.NeighbourhoodSystems
