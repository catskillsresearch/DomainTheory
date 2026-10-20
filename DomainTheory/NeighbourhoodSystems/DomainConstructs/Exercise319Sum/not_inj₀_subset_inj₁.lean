module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β α' β' : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}

variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

variable {h₀' : ∀ X, V₀'.mem X → X.Nonempty} {h₁' : ∀ Y, V₁'.mem Y → Y.Nonempty}

/-- A nonempty left copy is never contained in a right copy. -/
theorem not_inj₀_subset_inj₁ {X : Set α} {Y : Set β} (hX : X.Nonempty)
    (hsub : (inj₀ X : Set (Option (α ⊕ β))) ⊆ inj₁ Y) : False := by
  obtain ⟨a, ha⟩ := hX
  exact il_mem_inj₁ (hsub (il_mem_inj₀.mpr ha))

end DomainTheory.NeighbourhoodSystems
