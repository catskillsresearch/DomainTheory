module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Finset.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}


variable {D : ∀ i, NeighborhoodSystem (α i)}


theorem injI_nonempty {i : ι} {X : Set (α i)} (hX : X.Nonempty) : (injI i X).Nonempty := by
  obtain ⟨a, ha⟩ := hX; exact ⟨some ⟨i, a⟩, some_mem_injI.mpr ha⟩

end Exercise629
end DomainTheory.NeighbourhoodSystems
