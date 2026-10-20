module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.ScottPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashEnum
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashEnum_proper
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashEnum_master

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

/-- Every enumerated smash neighbourhood is a product `prodNbhd A B` of component neighbourhoods
(the proper form, or the master `prodNbhd Δ₀ Δ₁`). -/
theorem smashEnum_eq_prodNbhd_mem (k : ℕ) :
    ∃ A B, V₀.mem A ∧ V₁.mem B ∧ smashEnum P₀ P₁ k = prodNbhd A B := by
  by_cases h : P₀.X k.unpair.1 ≠ V₀.master ∧ P₁.X k.unpair.2 ≠ V₁.master
  · exact ⟨_, _, P₀.mem_X _, P₁.mem_X _, smashEnum_proper h⟩
  · exact ⟨_, _, V₀.master_mem, V₁.master_mem, smashEnum_master h⟩

end Smash

end DomainTheory.NeighbourhoodSystems
