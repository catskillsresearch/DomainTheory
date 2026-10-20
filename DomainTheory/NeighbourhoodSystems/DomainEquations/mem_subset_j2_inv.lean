module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition63
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516
public import DomainTheory.NeighbourhoodSystems.DomainEquations.StrictDomainObj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Inst3
public import DomainTheory.NeighbourhoodSystems.DomainEquations.id_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.comp_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.tcObj_sys

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

universe w

section ShapeLemmas

open Example62C

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  {V₂ : NeighborhoodSystem γ} {h₀ : ∀ X, V₀.mem X → X.Nonempty}
  {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty} {h₂ : ∀ Z, V₂.mem Z → Z.Nonempty}

/-- A `sum3`-neighbourhood contained in a `2`-copy `2Z` is itself a `2`-copy. -/
theorem mem_subset_j2_inv {W : Set (Option (α ⊕ β ⊕ γ))} {Z : Set γ}
    (hW : (sum3 V₀ V₁ V₂ h₀ h₁ h₂).mem W) (hsub : W ⊆ j2 Z) :
    ∃ Z₂, V₂.mem Z₂ ∧ W = j2 Z₂ := by
  rcases hW with rfl | ⟨X₂, hX₂, rfl⟩ | ⟨Y₂, hY₂, rfl⟩ | ⟨Z₂, hZ₂, rfl⟩
  · exact absurd (hsub none_mem_master3) none_not_mem_j2
  · obtain ⟨a, ha⟩ := h₀ X₂ hX₂; exact absurd (hsub (t0_mem_j0.mpr ha)) t0_not_mem_j2
  · obtain ⟨b, hb⟩ := h₁ Y₂ hY₂; exact absurd (hsub (t1_mem_j1.mpr hb)) t1_not_mem_j2
  · exact ⟨Z₂, hZ₂, rfl⟩

end ShapeLemmas

end DomainTheory.NeighbourhoodSystems
