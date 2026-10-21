/-ai
iprodEquiv is the order isomorphism between the elements of the indexed product and the pointwise product of the factor element domains, sending a product element to its family of projections and a family of elements to the product element assembled from them.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import Mathlib.Data.Set.Finite.Basic
import all Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Finset.Basic
import all Mathlib.Data.Finset.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.mem_iprodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.iprod
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.updTuple_apply_self
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.iprod_mem_slice
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.iprodNbhd_subset_slice
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.proj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.fromPi
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.z_mem_of_slices
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.fromPi_toPi
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.proj_fromPi

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

/-- **Exercise 6.29 — `×` generalizes to `∏`, correct up to isomorphism.** The domain of the
indexed product is the pointwise product of the factor domains: `|∏_i D_i| ≃o ∀ i, |D_i|`. This is
the infinitary **Proposition 3.2** (`prodEquiv`). -/
def iprodEquiv (D : ∀ i, NeighborhoodSystem (α i)) :
    (iprod D).Element ≃o (∀ i, (D i).Element) where
  toFun z := fun i => proj z i
  invFun x := fromPi D x
  left_inv z := fromPi_toPi z
  right_inv x := funext fun i => proj_fromPi x i
  map_rel_iff' := by
    intro z z'
    constructor
    · intro h W hzW
      obtain ⟨X, hXmem, hXf, rfl⟩ := z.sub hzW
      refine z_mem_of_slices z' hXmem hXf fun i => ?_
      have hzi : (proj z i).mem (X i) :=
        ⟨hXmem i, z.up_mem hzW (iprod_mem_slice (hXmem i)) (iprodNbhd_subset_slice hXmem i)⟩
      exact ((h i) (X i) hzi).2
    · intro h i U hU
      exact ⟨hU.1, h _ hU.2⟩

end Iso

end IndexedProduct

end Exercise629

end DomainTheory.NeighbourhoodSystems
