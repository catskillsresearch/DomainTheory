module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Finset.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.iprodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.mem_iprodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.iprod
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.updTuple
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.updTuple_apply_self
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.updTuple_apply_ne
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.slice
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.iprod_mem_slice
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.iprod_mem_slice_inv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.slice_inter
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.slice_subset

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

/-- **The `i`-th component of a product element** (Scott's `z_i`). -/
def proj (z : (iprod D).Element) (i : ι) : (D i).Element where
  mem U := (D i).mem U ∧ z.mem (slice D i U)
  sub h := h.1
  master_mem := ⟨(D i).master_mem, by
    have : slice D i (D i).master = (iprod D).master := by
      show iprodNbhd (updTuple D i (D i).master) = iprodNbhd (fun j => (D j).master)
      congr 1; funext j
      by_cases h : j = i
      · subst h; rw [updTuple_apply_self]
      · rw [updTuple_apply_ne (D i).master h]
    rw [this]; exact z.master_mem⟩
  inter_mem := by
    rintro U U' ⟨_, hzU⟩ ⟨_, hzU'⟩
    have hz := z.inter_mem hzU hzU'
    rw [slice_inter] at hz
    exact ⟨iprod_mem_slice_inv (z.sub hz), hz⟩
  up_mem := by
    rintro U U' ⟨_, hzU⟩ hU' hUU'
    exact ⟨hU', z.up_mem hzU (iprod_mem_slice hU') (slice_subset i hUU')⟩

end Iso

end IndexedProduct

end Exercise629

end DomainTheory.NeighbourhoodSystems
