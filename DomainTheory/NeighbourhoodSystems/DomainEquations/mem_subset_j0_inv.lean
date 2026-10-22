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

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510


section ShapeLemmas

open Example62C

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  {V₂ : NeighborhoodSystem γ} {h₀ : ∀ X, V₀.mem X → X.Nonempty}
  {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty} {h₂ : ∀ Z, V₂.mem Z → Z.Nonempty}

/-- A `sum3`-neighbourhood contained in a `0`-copy `0X` is itself a `0`-copy. -/
theorem mem_subset_j0_inv {W : Set (Option (α ⊕ β ⊕ γ))} {X : Set α}
    (hW : (sum3 V₀ V₁ V₂ h₀ h₁ h₂).mem W) (hsub : W ⊆ j0 X) :
    ∃ X₂, V₀.mem X₂ ∧ W = j0 X₂ := by
  rcases hW with rfl | ⟨X₂, hX₂, rfl⟩ | ⟨Y₂, hY₂, rfl⟩ | ⟨Z₂, hZ₂, rfl⟩
  · exact absurd (hsub none_mem_master3) none_not_mem_j0
  · exact ⟨X₂, hX₂, rfl⟩
  · obtain ⟨b, hb⟩ := h₁ Y₂ hY₂; exact absurd (hsub (t1_mem_j1.mpr hb)) t1_not_mem_j0
  · obtain ⟨c, hc⟩ := h₂ Z₂ hZ₂; exact absurd (hsub (t2_mem_j2.mpr hc)) t2_not_mem_j0

end ShapeLemmas

end DomainTheory.NeighbourhoodSystems
