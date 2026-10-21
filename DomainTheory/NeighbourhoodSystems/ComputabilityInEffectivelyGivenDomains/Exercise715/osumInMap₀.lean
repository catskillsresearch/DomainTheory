/-ai
The coalesced left injection relates a left neighbourhood X to a coalesced neighbourhood W when the left injection of X is contained in W. The master is related because the left injection of the left master lies under the coalesced master. If X is the left master, both related codomain neighbourhoods equal the coalesced master, so their intersection does too; otherwise that intersection is a coalesced neighbourhood containing the injection. The relation is monotone because left injection preserves inclusion.
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
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.osum_eq_master_of_inj₀master

@[expose] public section

set_option linter.unusedSectionVars false

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

/-- **Coalesced left injection `in₀ : 𝒟₀ → 𝒟₀ ⊕ 𝒟₁`**, `X (in₀) W ↔ inj₀ X ⊆ W`. -/
def osumInMap₀ : ApproximableMap V₀ (osum h₀ h₁) where
  rel X W := V₀.mem X ∧ (osum h₀ h₁).mem W ∧ inj₀ X ⊆ W
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨V₀.master_mem, (osum h₀ h₁).master_mem, inj₀_subset_sumMaster V₀.master_mem⟩
  inter_right := by
    rintro X W W' ⟨hX, hW, hsub⟩ ⟨-, hW', hsub'⟩
    refine ⟨hX, ?_, Set.subset_inter hsub hsub'⟩
    by_cases hXm : X = V₀.master
    · subst hXm
      rw [osum_eq_master_of_inj₀master hW hsub, osum_eq_master_of_inj₀master hW' hsub',
        Set.inter_self]
      exact (osum h₀ h₁).master_mem
    · exact (osum h₀ h₁).inter_mem hW hW' (Or.inr (Or.inl ⟨X, hX, hXm, rfl⟩))
        (Set.subset_inter hsub hsub')
  mono := by
    rintro X X' W W' ⟨_, _, hsub⟩ hX'X hWW' hX' hW'
    exact ⟨hX', hW', (inj₀_subset_inj₀.mpr hX'X).trans (hsub.trans hWW')⟩

end Coalesced

end DomainTheory.NeighbourhoodSystems
