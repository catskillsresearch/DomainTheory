/-ai
Projecting, at an index i, the element assembled from a tuple of components recovers the i-th component.

Extensionality of elements reduces the claim to a neighbourhood U. If the projection contains U, the assembled element contains the corresponding slice, which means the component contains U. If the component contains U, then U is a neighbourhood and the assembled element contains the slice.
ai-/
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
