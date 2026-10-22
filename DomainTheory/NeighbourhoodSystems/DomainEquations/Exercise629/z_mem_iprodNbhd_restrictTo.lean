/-ai
An element of the indexed product that contains every slice of a family, with each set contained in the corresponding master, contains the product neighbourhood of the restriction of that family to any finite list.

Proceed by induction on the list. The empty restriction is the family of masters, which is the master of the product, and the element contains the master. For a cons-list, the restricted product neighbourhood is the head slice intersected with the restriction to the tail, and the element contains both factors.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Finset.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.iprodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.mem_iprodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.iprod
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.updTuple_apply_self
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.slice
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.restrictTo
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.iprodNbhd_restrictTo_cons

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

/-- An element contains the restricted cylinder once it contains each listed slice. -/
theorem z_mem_iprodNbhd_restrictTo (z : (iprod D).Element) {X : ∀ i, Set (α i)}
    (hXsub : ∀ i, X i ⊆ (D i).master) (hslice : ∀ i, z.mem (slice D i (X i))) (l : List ι) :
    z.mem (iprodNbhd (restrictTo D l X)) := by
  induction l with
  | nil =>
    have : restrictTo D [] X = fun j => (D j).master := by
      funext j; rw [restrictTo]; exact ite_eq_right List.not_mem_nil
    rw [this]; exact z.master_mem
  | cons a l ih =>
    rw [iprodNbhd_restrictTo_cons hXsub a l]
    exact z.inter_mem (hslice a) ih

end Iso

end IndexedProduct

end Exercise629

end DomainTheory.NeighbourhoodSystems
