module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition81
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {D E : NeighborhoodSystem α}

namespace Subsystem

/-- **Proposition 8.2's retraction `a = i ∘ j`.** As a neighbourhood relation (unfolding `inj`/
`proj`), `X a Z ↔ ∃ Y ∈ D, X ⊆ Y ⊆ Z` — exactly Scott's formula. -/
def retractionOfSubsystem (h : D ◁ E) : ApproximableMap E E := h.inj.comp h.proj

end Subsystem

end DomainTheory.NeighbourhoodSystems
