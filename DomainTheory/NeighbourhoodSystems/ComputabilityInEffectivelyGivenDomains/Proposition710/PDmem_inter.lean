/-ai
The family of power-domain neighbourhoods is closed under binary intersection.

Write the first neighbourhood as a finite union of down-sets. Its intersection with the second neighbourhood is a power-domain neighbourhood by the lemma on intersections with such a union.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition79
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PDmem_biUnion_inter

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **`ℙ𝒟` is closed under binary intersection.** (The content of Part A's condition (ii).) -/
theorem PDmem_inter {W₁ W₂ : Set (Set α)} (h₁ : V.PDmem W₁) (h₂ : V.PDmem W₂) :
    V.PDmem (W₁ ∩ W₂) := by
  obtain ⟨L₁, hL₁, rfl⟩ := h₁
  exact V.PDmem_biUnion_inter L₁ hL₁ h₂

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
