module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.retraction
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition_8_1

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap Subsystem

/-- Scott's Proposition 8.2: the endomap of a subdomain embedding is a retraction,
and the subdomain's elements are isomorphic to that retraction's fixed points. -/
theorem proposition_82 :
    (∀ {α : Type*} {D E : NeighborhoodSystem α} (h : D ◁ E),
      Retraction (retractionOfSubsystem h)) ∧
    (∀ {α : Type*} {D E : NeighborhoodSystem α} (h : D ◁ E),
      Retraction (retractionOfSubsystem h) ∧
        Nonempty (D.Element ≃o {y : E.Element // (retractionOfSubsystem h).toElementMap y = y})) :=
  ⟨@isRetraction_retractionOfSubsystem, @retraction_of_subsystem⟩

end DomainTheory.NeighbourhoodSystems
