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

open scoped Classical in
/-- **Coalesced-sum enumeration.** Tag `0`/`1`/`≥2`; a tag-0/1 code is its proper left/right copy
when the indexed factor is proper, otherwise it is re-routed to the master (the classical input). -/
noncomputable def osumEnum (t : ℕ) : Set (Option (α ⊕ β)) :=
  if t.unpair.1 = 0 ∧ P₀.X t.unpair.2 ≠ V₀.master then inj₀ (P₀.X t.unpair.2)
  else if t.unpair.1 = 1 ∧ P₁.X t.unpair.2 ≠ V₁.master then inj₁ (P₁.X t.unpair.2)
  else sumMaster V₀ V₁

end Coalesced

end DomainTheory.NeighbourhoodSystems
