/-ai
A nonempty right copy is not contained in a left copy.

A token of the nonempty set has its right tag in the right copy and hence in the left copy, but no right tag lies in a left copy.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β α' β' : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}

variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

variable {h₀' : ∀ X, V₀'.mem X → X.Nonempty} {h₁' : ∀ Y, V₁'.mem Y → Y.Nonempty}

/-- A nonempty right copy is never contained in a left copy. -/
theorem not_inj₁_subset_inj₀ {X : Set α} {Y : Set β} (hY : Y.Nonempty)
    (hsub : (inj₁ Y : Set (Option (α ⊕ β))) ⊆ inj₀ X) : False := by
  obtain ⟨b, hb⟩ := hY
  exact ir_mem_inj₀ (hsub (ir_mem_inj₁.mpr hb))

end DomainTheory.NeighbourhoodSystems
