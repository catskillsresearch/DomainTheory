module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Finset.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.iprodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.mem_iprodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.FinSupp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.iprod
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.updTuple_apply_self
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.slice
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.restrictTo
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.z_mem_iprodNbhd_restrictTo

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

/-- **Reconstruction.** A product element containing each of a cylinder's slices contains the
cylinder. The finite support (a *list* of coordinates) lets the only finitely many non-trivial slices
be intersected inside the element — entirely choice-free. -/
theorem z_mem_of_slices (z : (iprod D).Element) {X : ∀ i, Set (α i)}
    (hXmem : ∀ i, (D i).mem (X i)) (hXf : FinSupp D X)
    (hslice : ∀ i, z.mem (slice D i (X i))) : z.mem (iprodNbhd X) := by
  obtain ⟨l, hl⟩ := hXf
  have hsub : ∀ i, X i ⊆ (D i).master := fun i => (D i).sub_master (hXmem i)
  have key := z_mem_iprodNbhd_restrictTo z hsub hslice l
  have heq : restrictTo D l X = X := by
    funext j
    rw [restrictTo]
    by_cases h : j ∈ l
    · rw [ite_eq_left h]
    · rw [ite_eq_right h]; exact (hl j h).symm
  rwa [heq] at key

end Iso

end IndexedProduct

end Exercise629

end DomainTheory.NeighbourhoodSystems
