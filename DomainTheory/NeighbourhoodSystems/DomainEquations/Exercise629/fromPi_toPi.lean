module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Finset.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.mem_iprodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.iprod
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.updTuple_apply_self
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.iprod_mem_slice
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.iprodNbhd_subset_slice
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.proj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.fromPi
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.z_mem_of_slices

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

theorem fromPi_toPi (z : (iprod D).Element) : fromPi D (fun i => proj z i) = z := by
  apply Element.ext
  intro W
  constructor
  · rintro ⟨X, hX, hXf, rfl⟩
    exact z_mem_of_slices z (fun i => (hX i).1) hXf (fun i => (hX i).2)
  · intro hW
    obtain ⟨X, hXmem, hXf, rfl⟩ := z.sub hW
    exact ⟨X, fun i => ⟨hXmem i, z.up_mem hW (iprod_mem_slice (hXmem i))
      (iprodNbhd_subset_slice hXmem i)⟩, hXf, rfl⟩

end Iso

end IndexedProduct

end Exercise629

end DomainTheory.NeighbourhoodSystems
