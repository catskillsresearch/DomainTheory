/-ai
The retraction of a subsystem lies under the identity map.

A related pair of neighbourhoods yields, by the relation criterion, an intermediate neighbourhood of the subsystem lying between them, and transitivity of inclusion gives the identity relation.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition82
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {D E : NeighborhoodSystem α}


namespace Subsystem

variable {h : D ◁ E}

/-- **Scott's remark before Definition 8.3.** Every retraction `a = retractionOfSubsystem h` of
Proposition 8.2 satisfies `a ⊑ I_E`: unwinding `X a Z ↔ ∃ Y ∈ D, X ⊆ Y ⊆ Z` gives `X ⊆ Z`
directly. -/
theorem retractionOfSubsystem_le_idMap (h : D ◁ E) : retractionOfSubsystem h ≤ idMap E := by
  intro X Z hr
  obtain ⟨hEX, hEZ, Y, _, hXY, hYZ⟩ := (retractionOfSubsystem_rel h).mp hr
  exact ⟨hEX, hEZ, hXY.trans hYZ⟩

end Subsystem
end DomainTheory.NeighbourhoodSystems
