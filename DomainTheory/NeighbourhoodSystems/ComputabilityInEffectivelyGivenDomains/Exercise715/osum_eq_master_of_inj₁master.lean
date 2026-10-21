/-ai
A coalesced neighbourhood that contains the right injection of the right master equals the separated-sum master.

The master case is immediate. A left copy cannot contain that injection, because a point of the nonempty right master lies in the right injection and not in the left injection. A proper right copy would contain the right master and therefore equal it.
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

theorem osum_eq_master_of_inj₁master {W : Set (Option (α ⊕ β))} (hW : (osum h₀ h₁).mem W)
    (hsub : inj₁ V₁.master ⊆ W) : W = sumMaster V₀ V₁ := by
  rcases hW with rfl | ⟨X', hX', -, rfl⟩ | ⟨Y', hY', hY'ne, rfl⟩
  · rfl
  · obtain ⟨b, hb⟩ := h₁ V₁.master V₁.master_mem
    exact absurd (hsub (ir_mem_inj₁.mpr hb)) ir_mem_inj₀
  · exact absurd (Set.Subset.antisymm (V₁.sub_master hY') (inj₁_subset_inj₁.mp hsub)) hY'ne

end Coalesced

end DomainTheory.NeighbourhoodSystems
