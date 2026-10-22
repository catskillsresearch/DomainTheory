module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Finset.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.mem_iprodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.updTuple_apply_self
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.proj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.fromPi
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.fromPi_mem_slice

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

theorem proj_fromPi (x : ∀ i, (D i).Element) (i : ι) : proj (fromPi D x) i = x i := by
  apply Element.ext
  intro U
  constructor
  · rintro ⟨_, hz⟩; exact (fromPi_mem_slice x i U).mp hz
  · intro hU; exact ⟨(x i).sub hU, (fromPi_mem_slice x i U).mpr hU⟩

end Iso

end IndexedProduct

end Exercise629

end DomainTheory.NeighbourhoodSystems
