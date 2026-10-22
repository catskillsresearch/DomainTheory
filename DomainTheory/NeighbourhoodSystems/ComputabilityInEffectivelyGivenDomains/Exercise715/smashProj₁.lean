module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.ScottPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashPresentation_X

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}

open Exercise510

section Smash

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

variable {P₀ P₁}

variable (P₀ P₁)

/-- **The smash projection `p₁ : 𝒟₀ ⊗ 𝒟₁ → 𝒟₁`**, `(X ∪ Y) p₁ Y' ↔ Y ⊆ Y'`. -/
def smashProj₁ (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    ApproximableMap (smash V₀ V₁) V₁ where
  rel W Y' := (smash V₀ V₁).mem W ∧ V₁.mem Y' ∧ Sum.inr ⁻¹' W ⊆ Y'
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(smash V₀ V₁).master_mem, V₁.master_mem, by simp⟩
  inter_right := by
    rintro W Y' Y'' ⟨hW, hY', hsub⟩ ⟨-, hY'', hsub'⟩
    obtain ⟨A, B, _, hB, rfl⟩ := smash_mem_prodNbhd_form hW
    rw [inr_preimage_prodNbhd] at hsub hsub' ⊢
    exact ⟨hW, V₁.inter_mem hY' hY'' hB (Set.subset_inter hsub hsub'), Set.subset_inter hsub hsub'⟩
  mono := by
    rintro W W₂ Y' Y₂' ⟨_, _, hsub⟩ hW₂W hY'Y₂' hW₂ hY₂'
    exact ⟨hW₂, hY₂', ((Set.preimage_mono hW₂W).trans hsub).trans hY'Y₂'⟩

end Smash

end DomainTheory.NeighbourhoodSystems
