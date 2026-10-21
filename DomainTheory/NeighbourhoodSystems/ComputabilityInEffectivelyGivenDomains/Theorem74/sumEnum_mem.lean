/-ai
Every enumerated set is a neighbourhood of the sum.

Unfold the enumeration and split on the two conditionals. Tag zero is a left copy of a neighbourhood of the first system, tag one is a right copy of a neighbourhood of the second system, and the remaining case is the master.
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

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ α' β' : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

section Sum

variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

variable {P₀ : ComputablePresentation V₀} {P₁ : ComputablePresentation V₁}

theorem sumEnum_mem (t : ℕ) : (sum V₀ V₁ h₀ h₁).mem (sumEnum P₀ P₁ t) := by
  unfold sumEnum
  split
  · exact Or.inr (Or.inl ⟨_, P₀.mem_X _, rfl⟩)
  · split
    · exact Or.inr (Or.inr ⟨_, P₁.mem_X _, rfl⟩)
    · exact Or.inl rfl

end Sum

end DomainTheory.NeighbourhoodSystems
