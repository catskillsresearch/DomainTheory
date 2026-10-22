/-ai
Equal product neighbourhoods come from equal families of sets.

Extensionality in the index and in each set reduces to membership of one dependent pair, which is membership in the corresponding coordinate of the product neighbourhood.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Finset.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.iprodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.mem_iprodNbhd

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

/-- The tuple representation of a product neighbourhood is unique. -/
theorem iprodNbhd_injective {X X' : ∀ i, Set (α i)} (h : iprodNbhd X = iprodNbhd X') : X = X' := by
  funext i; apply Set.ext; intro a
  simpa only [mem_iprodNbhd] using Set.ext_iff.mp h ⟨i, a⟩

end Exercise629

end DomainTheory.NeighbourhoodSystems
