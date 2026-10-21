/-ai
fromPi assembles an element of the indexed product from a tuple of component elements. A product neighbourhood belongs to the assembled element exactly when it is the product neighbourhood of a finitely supported tuple of sets, each belonging to the corresponding component.
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
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.iprodNbhd_subset_iff
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.FinSupp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.inter
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.iprod
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.updTuple_apply_self

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

/-- **The element of `∏_i D_i` assembled from a tuple of components.** -/
def fromPi (D : ∀ i, NeighborhoodSystem (α i)) (x : ∀ i, (D i).Element) : (iprod D).Element where
  mem W := ∃ X : ∀ i, Set (α i), (∀ i, (x i).mem (X i)) ∧ FinSupp D X ∧ W = iprodNbhd X
  sub := by rintro W ⟨X, hX, hXf, rfl⟩; exact ⟨X, fun i => (x i).sub (hX i), hXf, rfl⟩
  master_mem := ⟨fun i => (D i).master, fun i => (x i).master_mem, FinSupp.master, rfl⟩
  inter_mem := by
    rintro W W' ⟨X, hX, hXf, rfl⟩ ⟨X', hX', hX'f, rfl⟩
    exact ⟨fun i => X i ∩ X' i, fun i => (x i).inter_mem (hX i) (hX' i), hXf.inter hX'f,
      iprodNbhd_inter X X'⟩
  up_mem := by
    rintro W W' ⟨X, hX, _, rfl⟩ hW' hsub
    obtain ⟨X', hX'mem, hX'f, rfl⟩ := hW'
    rw [iprodNbhd_subset_iff] at hsub
    exact ⟨X', fun i => (x i).up_mem (hX i) (hX'mem i) (hsub i), hX'f, rfl⟩

end Iso

end IndexedProduct

end Exercise629

end DomainTheory.NeighbourhoodSystems
