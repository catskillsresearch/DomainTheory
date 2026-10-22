/-ai
If a set of left tokens is nonempty, the right content of its left copy is the master of the second system.

Simplification removes the right-tag clause and the basepoint clause, since neither lies in a left copy, and leaves membership in the second master together with a left tag in the copy. One direction forgets the tag. The other takes a token of the nonempty set and tags it on the left.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Insert
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.inj₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.il_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.ir_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.none_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.ir_mem_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.il_mem_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.none_mem_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.none_mem_sumMaster
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.il_preimage_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.ir_preimage_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.rightPart
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.mem_leftPart
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.mem_rightPart
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.leftPart_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.rightPart_inj₁

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)

variable {V₀ V₁}

theorem rightPart_inj₀ (V₁ : NeighborhoodSystem β) {X : Set α} (hX : X.Nonempty) :
    rightPart V₁ (inj₀ X : Set (Option (α ⊕ β))) = V₁.master := by
  ext b
  simp only [mem_rightPart, ir_mem_inj₀, none_mem_inj₀, or_false, false_or]
  constructor
  · rintro ⟨hb, _⟩; exact hb
  · intro hb; obtain ⟨a, ha⟩ := hX; exact ⟨hb, ⟨a, il_mem_inj₀.mpr ha⟩⟩

end DomainTheory.NeighbourhoodSystems
