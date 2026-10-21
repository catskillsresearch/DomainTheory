/-ai
A sum neighbourhood contained in a right copy is itself the right copy of a neighbourhood.

Split on the three forms of a sum neighbourhood. The master contains the basepoint, which lies in no right copy. A left copy of a neighbourhood is nonempty, so it contains a left tag, which lies in no right copy. A right copy is already of the required form.
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

/-- A sum-neighbourhood contained in a *right* copy `1Y` is itself a right copy `1Y₂`. -/
theorem mem_subset_inj₁ {W : Set (Option (α ⊕ β))} {Y : Set β}
    (hW : (sum V₀ V₁ h₀ h₁).mem W) (hsub : W ⊆ inj₁ Y) :
    ∃ Y₂, V₁.mem Y₂ ∧ W = inj₁ Y₂ := by
  rcases hW with rfl | ⟨X₂, hX₂, rfl⟩ | ⟨Y₂, hY₂, rfl⟩
  · exact absurd (hsub none_mem_sumMaster) none_mem_inj₁
  · obtain ⟨a, ha⟩ := h₀ X₂ hX₂
    exact absurd (hsub (il_mem_inj₀.mpr ha)) il_mem_inj₁
  · exact ⟨Y₂, hY₂, rfl⟩

end DomainTheory.NeighbourhoodSystems
