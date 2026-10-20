module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.ScottPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashPresentation_X
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashProj₀_rel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashProj₁_rel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashPaired_rel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.osum_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.osumEnum
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.osumEnum_left
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.osumEnum_right
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.osumEnum_master

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

include h₀ h₁ in
theorem osumEnum_nonempty (t : ℕ) : (osumEnum P₀ P₁ t).Nonempty := by
  by_cases hL : t.unpair.1 = 0 ∧ P₀.X t.unpair.2 ≠ V₀.master
  · rw [osumEnum_left hL]; exact inj₀_nonempty (h₀ _ (P₀.mem_X _))
  · by_cases hR : t.unpair.1 = 1 ∧ P₁.X t.unpair.2 ≠ V₁.master
    · rw [osumEnum_right hR]; exact inj₁_nonempty (h₁ _ (P₁.mem_X _))
    · rw [osumEnum_master hL hR]; exact ⟨none, none_mem_sumMaster⟩

end Coalesced

end DomainTheory.NeighbourhoodSystems
