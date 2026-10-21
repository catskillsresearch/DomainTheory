/-ai
One product neighbourhood is contained in another if and only if each coordinate set is contained in the corresponding set.

A token of a coordinate set is a dependent pair in the smaller product neighbourhood, hence in the larger one. Conversely, a dependent pair in the smaller neighbourhood has its second component in the smaller coordinate set, hence in the larger one.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import Mathlib.Data.Set.Finite.Basic
import all Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Finset.Basic
import all Mathlib.Data.Finset.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.iprodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.mem_iprodNbhd

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

/-- Inclusion of product neighbourhoods is coordinatewise (Scott's (1)). -/
theorem iprodNbhd_subset_iff {X X' : ∀ i, Set (α i)} :
    iprodNbhd X ⊆ iprodNbhd X' ↔ ∀ i, X i ⊆ X' i := by
  constructor
  · intro h i a ha; exact h (show (⟨i, a⟩ : Σ i, α i) ∈ iprodNbhd X from ha)
  · rintro h ⟨i, a⟩ ha; exact h i ha

end Exercise629

end DomainTheory.NeighbourhoodSystems
