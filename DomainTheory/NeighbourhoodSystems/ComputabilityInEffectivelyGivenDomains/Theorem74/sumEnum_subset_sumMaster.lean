/-ai
Every enumerated sum neighbourhood is contained in the sum master.

Unfold the enumeration and split. A left copy of a neighbourhood is contained in the master, a right copy of a neighbourhood is contained in the master, and the master is contained in itself.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.prodEnum_apply
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.prodPresentation_X
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.sumEnum
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.sumEnum_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.sumEnum_one

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ α' β' : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

section Sum

variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

variable {P₀ : ComputablePresentation V₀} {P₁ : ComputablePresentation V₁}

/-- Every enumerated sum-neighbourhood lies under the master (no non-emptiness needed). -/
theorem sumEnum_subset_sumMaster (n : ℕ) :
    sumEnum P₀ P₁ n ⊆ sumMaster V₀ V₁ := by
  unfold sumEnum
  split
  · exact inj₀_subset_sumMaster (P₀.mem_X _)
  · split
    · exact inj₁_subset_sumMaster (P₁.mem_X _)
    · exact subset_rfl

end Sum

end DomainTheory.NeighbourhoodSystems
