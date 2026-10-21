/-ai
A right-tagged token lies in the right copy of a set if and only if the underlying token lies in that set.

Unfold the right copy as the image of the right tag. An image witness is a token of the set whose tag equals the given tag; injectivity of the option and right-sum constructors identifies the two tokens, so membership transfers. In the other direction the given token is the image witness.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import Mathlib.Data.Set.Image
import all Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Insert
import all Mathlib.Data.Set.Insert
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.ir
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.inj₁
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.il_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.ir_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318.none_mem_inj₀

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}

@[simp] theorem ir_mem_inj₁ {Y : Set β} {b : β} : (ir b : Option (α ⊕ β)) ∈ inj₁ Y ↔ b ∈ Y := by
  simp only [inj₁, Set.mem_image, ir]
  constructor
  · rintro ⟨b', hb', hb⟩; simp only [Option.some.injEq, Sum.inr.injEq] at hb; exact hb ▸ hb'
  · intro hb; exact ⟨b, hb, rfl⟩

end DomainTheory.NeighbourhoodSystems
