/-ai
The left smash projection relates a smash neighbourhood W to a left neighbourhood X' when the left preimage of W is contained in X'. The master clause holds by simplification. Writing W as a product, the left preimage is the left factor, so the intersection of two targets contains that factor and is a left neighbourhood. The relation is monotone because preimages preserve inclusion.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.ScottPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashPresentation_X

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}

open Exercise510

section Smash

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

variable {P₀ P₁}

variable (P₀ P₁)

/-- **The smash projection `p₀ : 𝒟₀ ⊗ 𝒟₁ → 𝒟₀`**, `(X ∪ Y) p₀ X' ↔ X ⊆ X'`. -/
def smashProj₀ (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    ApproximableMap (smash V₀ V₁) V₀ where
  rel W X' := (smash V₀ V₁).mem W ∧ V₀.mem X' ∧ Sum.inl ⁻¹' W ⊆ X'
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(smash V₀ V₁).master_mem, V₀.master_mem, by simp⟩
  inter_right := by
    rintro W X' X'' ⟨hW, hX', hsub⟩ ⟨-, hX'', hsub'⟩
    obtain ⟨A, B, hA, _, rfl⟩ := smash_mem_prodNbhd_form hW
    rw [inl_preimage_prodNbhd] at hsub hsub' ⊢
    exact ⟨hW, V₀.inter_mem hX' hX'' hA (Set.subset_inter hsub hsub'), Set.subset_inter hsub hsub'⟩
  mono := by
    rintro W W₂ X' X₂' ⟨_, _, hsub⟩ hW₂W hX'X₂' hW₂ hX₂'
    exact ⟨hW₂, hX₂', ((Set.preimage_mono hW₂W).trans hsub).trans hX'X₂'⟩

end Smash

end DomainTheory.NeighbourhoodSystems
