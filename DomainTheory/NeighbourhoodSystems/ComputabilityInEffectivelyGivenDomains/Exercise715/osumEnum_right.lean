/-ai
If a code has tag 1 and indexes a proper right neighbourhood, the coalesced-sum enumeration returns the right injection of that neighbourhood.

The tag cannot also be 0, so the first conditional fails and the second conditional is the right-injection branch.
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
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.osum_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.osumEnum

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

open scoped Classical in
theorem osumEnum_right {t : ℕ} (h : t.unpair.1 = 1 ∧ P₁.X t.unpair.2 ≠ V₁.master) :
    osumEnum P₀ P₁ t = inj₁ (P₁.X t.unpair.2) := by
  have h0 : ¬(t.unpair.1 = 0 ∧ P₀.X t.unpair.2 ≠ V₀.master) := by
    rintro ⟨hc, -⟩; obtain ⟨h1, -⟩ := h; omega
  unfold osumEnum; rw [ite_eq_right h0, ite_eq_left h]

end Coalesced

end DomainTheory.NeighbourhoodSystems
