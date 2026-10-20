module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.prodEnum_apply
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.prodPresentation_X
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.sumEnum_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.sumEnum_one

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ α' β' : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

section Sum

variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

variable {P₀ : ComputablePresentation V₀} {P₁ : ComputablePresentation V₁}

/-- A nonempty left copy cannot equal a right copy. -/
theorem inj₀_eq_inj₁_elim {A : Set α} {B : Set β} (hA : A.Nonempty)
    (h : (inj₀ A : Set (Option (α ⊕ β))) = inj₁ B) : False := by
  obtain ⟨a, ha⟩ := hA; exact il_mem_inj₁ (h ▸ il_mem_inj₀.mpr ha)

end Sum

end DomainTheory.NeighbourhoodSystems
