/-ai
The coalesced right projection relates a coalesced neighbourhood W to a right neighbourhood Y when the right part of W is contained in Y. The right part of the separated-sum master is contained in the right master. The right part of a right injection is the injected neighbourhood, and the right part of the master or of a left injection is the right master, so an intersection of targets still contains the right part and is a right neighbourhood. The relation is monotone because the right part preserves inclusion.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.ScottPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashPresentation_X
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashProj₀_rel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashProj₁_rel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashPaired_rel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.osum
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.osum_master

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}

open Exercise510

section Coalesced

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty)

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

variable {P₀ P₁}

variable {h₀ h₁}

/-- **Coalesced right projection `out₁ : 𝒟₀ ⊕ 𝒟₁ → 𝒟₁`**. -/
def osumOutMap₁ : ApproximableMap (osum h₀ h₁) V₁ where
  rel W Y := (osum h₀ h₁).mem W ∧ V₁.mem Y ∧ rightPart V₁ W ⊆ Y
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(osum h₀ h₁).master_mem, V₁.master_mem, (rightPart_sumMaster V₀ V₁).subset⟩
  inter_right := by
    rintro W Y Y' ⟨hW, hY, hsub⟩ ⟨-, hY', hsub'⟩
    refine ⟨hW, V₁.inter_mem hY hY' ?_ (Set.subset_inter hsub hsub'), Set.subset_inter hsub hsub'⟩
    rcases hW with rfl | ⟨A, hA, -, rfl⟩ | ⟨B, hB, -, rfl⟩
    · rw [rightPart_sumMaster]; exact V₁.master_mem
    · rw [rightPart_inj₀ V₁ (h₀ A hA)]; exact V₁.master_mem
    · rw [rightPart_inj₁]; exact hB
  mono := by
    rintro W W' Y Y' ⟨_, _, hsub⟩ hW'W hYY' hW' hY'
    exact ⟨hW', hY', (rightPart_mono V₁ hW'W).trans (hsub.trans hYY')⟩

end Coalesced

end DomainTheory.NeighbourhoodSystems
