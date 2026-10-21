/-ai
One tagged copy at an index is contained in another if and only if the underlying set is contained in the other.

A token of the smaller set tags to a token of the smaller copy, hence of the larger copy, and therefore lies in the larger set. Conversely, every token of the smaller copy is the tag of a token of the smaller set, which lies in the larger set.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import Mathlib.Data.Set.Finite.Basic
import all Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Finset.Basic
import all Mathlib.Data.Finset.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.mem_iprodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.updTuple_apply_self
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.injI
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.some_mem_injI

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

theorem injI_subset_iff {i : ι} {X Y : Set (α i)} : injI i X ⊆ injI i Y ↔ X ⊆ Y := by
  constructor
  · intro h a ha; exact some_mem_injI.mp (h (some_mem_injI.mpr ha))
  · intro h; rintro w ⟨a, ha, rfl⟩; exact ⟨a, h ha, rfl⟩

end Exercise629

end DomainTheory.NeighbourhoodSystems
