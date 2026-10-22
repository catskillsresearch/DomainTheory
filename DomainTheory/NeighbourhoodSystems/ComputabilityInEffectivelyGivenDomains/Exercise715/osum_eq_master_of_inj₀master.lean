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

/-- An `osum`-member containing `inj₀ Δ₀` is forced to be the master (the bottom-collapse: the only
proper copy `⊇ inj₀ Δ₀` would need `Δ₀ ⊆ X` with `X ≠ Δ₀`). -/
theorem osum_eq_master_of_inj₀master {W : Set (Option (α ⊕ β))} (hW : (osum h₀ h₁).mem W)
    (hsub : inj₀ V₀.master ⊆ W) : W = sumMaster V₀ V₁ := by
  rcases hW with rfl | ⟨X', hX', hX'ne, rfl⟩ | ⟨Y', hY', -, rfl⟩
  · rfl
  · exact absurd (Set.Subset.antisymm (V₀.sub_master hX') (inj₀_subset_inj₀.mp hsub)) hX'ne
  · obtain ⟨a, ha⟩ := h₀ V₀.master V₀.master_mem
    exact absurd (hsub (il_mem_inj₀.mpr ha)) il_mem_inj₁

end Coalesced

end DomainTheory.NeighbourhoodSystems
