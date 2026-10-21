/-ai
A coalesced neighbourhood contained in a left injection is the left injection of a proper left neighbourhood.

The master contains the empty option, which no left injection contains. A right injection of a nonempty neighbourhood is not contained in a left injection. The remaining case is already a proper left copy.
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
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.osumPresentation_X

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

variable (P₀ P₁)

section CoalescedFunctor

variable {α' β' : Type*} {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}
  (h₀' : ∀ X, V₀'.mem X → X.Nonempty) (h₁' : ∀ Y, V₁'.mem Y → Y.Nonempty)

/-- An `osum`-member `⊆ inj₀ X` is a *proper* left copy. -/
theorem osum_mem_subset_inj₀ {W : Set (Option (α ⊕ β))} {X : Set α}
    (hW : (osum h₀ h₁).mem W) (hsub : W ⊆ inj₀ X) :
    ∃ X₂, V₀.mem X₂ ∧ X₂ ≠ V₀.master ∧ W = inj₀ X₂ := by
  rcases hW with rfl | ⟨X₂, hX₂, hne, rfl⟩ | ⟨Y₂, hY₂, hne, rfl⟩
  · exact absurd (hsub none_mem_sumMaster) none_mem_inj₀
  · exact ⟨X₂, hX₂, hne, rfl⟩
  · obtain ⟨b, hb⟩ := h₁ Y₂ hY₂; exact absurd (hsub (ir_mem_inj₁.mpr hb)) ir_mem_inj₀

end CoalescedFunctor

end Coalesced

end DomainTheory.NeighbourhoodSystems
