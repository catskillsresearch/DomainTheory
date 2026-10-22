/-ai
A dependent pair lies in a product neighbourhood if and only if its second component lies in the set at its first component.

Both sides are the defining membership of a product neighbourhood.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Finset.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.iprodNbhd

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

@[simp] theorem mem_iprodNbhd {X : ∀ i, Set (α i)} {i : ι} {a : α i} :
    (⟨i, a⟩ : Σ i, α i) ∈ iprodNbhd X ↔ a ∈ X i := Iff.rfl

end Exercise629

end DomainTheory.NeighbourhoodSystems
