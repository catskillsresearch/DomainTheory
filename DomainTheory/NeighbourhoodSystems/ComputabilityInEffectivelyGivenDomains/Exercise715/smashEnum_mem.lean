module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.ScottPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashEnum
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashEnum_proper
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashEnum_master

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}

open Exercise510

section Smash

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

variable {P₀ P₁}

theorem smashEnum_mem (t : ℕ) : (smash V₀ V₁).mem (smashEnum P₀ P₁ t) := by
  by_cases h : P₀.X t.unpair.1 ≠ V₀.master ∧ P₁.X t.unpair.2 ≠ V₁.master
  · rw [smashEnum_proper h]; exact smash_mem_proper (P₀.mem_X _) h.1 (P₁.mem_X _) h.2
  · rw [smashEnum_master h]; exact (smash V₀ V₁).master_mem

end Smash

end DomainTheory.NeighbourhoodSystems
