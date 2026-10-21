/-ai
If every set of a family is contained in the master of its system, then the product neighbourhood of the restriction to a cons-list is the slice at the head intersected with the product neighbourhood of the restriction to the tail.

The slice is a product neighbourhood, so the intersection law reduces the claim to equality of families. At the head, the restricted family is the head set, and the other side is that set intersected with itself or with the master, which contains it. Off the head, the one-coordinate update is the master and membership in the cons-list is membership in the tail, so both sides equal the tail restriction.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import Mathlib.Data.Set.Finite.Basic
import all Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Finset.Basic
import all Mathlib.Data.Finset.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.iprodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.mem_iprodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.iprodNbhd_inter
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.updTuple
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.updTuple_apply_self
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.updTuple_apply_ne
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.slice
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.slice_eq
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.restrictTo

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
theorem iprodNbhd_restrictTo_cons {X : ∀ i, Set (α i)} (hXsub : ∀ i, X i ⊆ (D i).master)
    (a : ι) (l : List ι) :
    iprodNbhd (restrictTo D (a :: l) X) = slice D a (X a) ∩ iprodNbhd (restrictTo D l X) := by
  rw [slice_eq, iprodNbhd_inter]
  congr 1; funext j
  show (if j ∈ a :: l then X j else (D j).master)
      = updTuple D a (X a) j ∩ (if j ∈ l then X j else (D j).master)
  by_cases hja : j = a
  · subst hja
    rw [updTuple_apply_self]
    by_cases hjl : j ∈ l
    · rw [ite_eq_left List.mem_cons_self, ite_eq_left hjl, Set.inter_self]
    · rw [ite_eq_left List.mem_cons_self, ite_eq_right hjl, Set.inter_eq_left.mpr (hXsub j)]
  · rw [updTuple_apply_ne (X a) hja]
    by_cases hjl : j ∈ l
    · rw [ite_eq_left (List.mem_cons_of_mem a hjl), ite_eq_left hjl, Set.inter_eq_right.mpr (hXsub j)]
    · rw [ite_eq_right fun h => (List.mem_cons.mp h).elim hja hjl, ite_eq_right hjl, Set.inter_self]

end Iso

end IndexedProduct

end Exercise629

end DomainTheory.NeighbourhoodSystems
