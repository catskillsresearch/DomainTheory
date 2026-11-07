module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.retraction

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {D E : NeighborhoodSystem α}

/-- A retraction is finitary when its fixed-point set is order-isomorphic to the
elements of some neighbourhood system. -/
def IsFinitary (a : ApproximableMap E E) : Prop :=
  ∃ (β : Type u) (F : NeighborhoodSystem β),
    Nonempty ({y : E.Element // a.toElementMap y = y} ≃o F.Element)

/-- A projection is a retraction lying below the identity. -/
def IsProjection (a : ApproximableMap E E) : Prop := Retraction a ∧ a ≤ idMap E

/-- A finitary projection is a projection whose fixed-point set is a domain. -/
class FinitaryProjection (a : ApproximableMap E E) : Prop where
  out : IsProjection a ∧ IsFinitary a

namespace Subsystem

theorem isFinitary_retractionOfSubsystem (h : D ◁ E) :
    IsFinitary (retractionOfSubsystem h) :=
  ⟨α, D, ⟨(elementIso h).symm⟩⟩

theorem retractionOfSubsystem_le_idMap (h : D ◁ E) : retractionOfSubsystem h ≤ idMap E := by
  intro X Z hr
  obtain ⟨hEX, hEZ, Y, _, hXY, hYZ⟩ := (retractionOfSubsystem_rel h).mp hr
  exact ⟨hEX, hEZ, hXY.trans hYZ⟩

theorem isProjection_retractionOfSubsystem (h : D ◁ E) :
    IsProjection (retractionOfSubsystem h) :=
  ⟨isRetraction_retractionOfSubsystem h, retractionOfSubsystem_le_idMap h⟩

theorem isFinitaryProjection_retractionOfSubsystem (h : D ◁ E) :
    FinitaryProjection (retractionOfSubsystem h) :=
  ⟨⟨isProjection_retractionOfSubsystem h, isFinitary_retractionOfSubsystem h⟩⟩

end Subsystem
end DomainTheory.NeighbourhoodSystems
