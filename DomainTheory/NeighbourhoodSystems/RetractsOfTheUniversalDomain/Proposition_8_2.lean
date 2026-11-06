module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition_8_1

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem ApproximableMap
variable {α : Type*} {D E : NeighborhoodSystem α}
namespace Subsystem

theorem retraction_of_subsystem (h : D ◁ E) :
    Retraction (retractionOfSubsystem h) ∧
      Nonempty (D.Element ≃o {y : E.Element // (retractionOfSubsystem h).toElementMap y = y}) :=
  ⟨isRetraction_retractionOfSubsystem h, ⟨elementIso h⟩⟩

end Subsystem
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.Subsystem
open NeighborhoodSystem ApproximableMap

theorem theorem_82 :
    (∀ {α : Type*} {D E : NeighborhoodSystem α} (h : D ◁ E),
      Retraction (retractionOfSubsystem h)) ∧
    (∀ {α : Type*} {D E : NeighborhoodSystem α} (h : D ◁ E),
      Retraction (retractionOfSubsystem h) ∧
        Nonempty (D.Element ≃o {y : E.Element // (retractionOfSubsystem h).toElementMap y = y})) :=
  ⟨@isRetraction_retractionOfSubsystem, @retraction_of_subsystem⟩

end DomainTheory.NeighbourhoodSystems.Subsystem
namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {D E : NeighborhoodSystem α}

def IsFinitary (a : ApproximableMap E E) : Prop :=
  ∃ (β : Type u) (F : NeighborhoodSystem β),
    Nonempty ({y : E.Element // a.toElementMap y = y} ≃o F.Element)

end
end DomainTheory.NeighbourhoodSystems
