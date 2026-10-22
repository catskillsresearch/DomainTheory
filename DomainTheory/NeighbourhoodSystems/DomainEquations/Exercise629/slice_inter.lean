/-ai
The intersection of two slices at the same index is the slice of the intersection of their data.

Each slice is a product neighbourhood of a one-coordinate update, so the intersection law reduces the claim to a coordinatewise equality. At the chosen index each update is the corresponding data set. At every other index each update is the master, and the master intersected with itself is the master.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Finset.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.mem_iprodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.iprodNbhd_inter
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
/-- Slices at the same coordinate intersect by intersecting their data. -/
theorem slice_inter (i : ι) (U U' : Set (α i)) :
    slice D i U ∩ slice D i U' = slice D i (U ∩ U') := by
  rw [slice_eq, slice_eq, slice_eq, iprodNbhd_inter]
  congr 1; funext j
  by_cases h : j = i
  · subst h; rw [updTuple_apply_self, updTuple_apply_self, updTuple_apply_self]
  · rw [updTuple_apply_ne U h, updTuple_apply_ne U' h, updTuple_apply_ne (U ∩ U') h,
      Set.inter_self]

end Iso

end IndexedProduct

end Exercise629

end DomainTheory.NeighbourhoodSystems
