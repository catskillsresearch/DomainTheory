module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition81
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition82.retractionOfSubsystem

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {D E : NeighborhoodSystem α}

namespace Subsystem

@[simp] theorem retractionOfSubsystem_rel (h : D ◁ E) {X Z : Set α} :
    (retractionOfSubsystem h).rel X Z ↔ E.mem X ∧ E.mem Z ∧ ∃ Y, D.mem Y ∧ X ⊆ Y ∧ Y ⊆ Z := by
  simp only [retractionOfSubsystem, comp_rel, inj_rel, proj_rel]
  constructor
  · rintro ⟨Y, ⟨hEX, hDY, hXY⟩, hDY', hEZ, hYZ⟩
    exact ⟨hEX, hEZ, Y, hDY, hXY, hYZ⟩
  · rintro ⟨hEX, hEZ, Y, hDY, hXY, hYZ⟩
    exact ⟨Y, ⟨hEX, hDY, hXY⟩, hDY, hEZ, hYZ⟩

end Subsystem

end DomainTheory.NeighbourhoodSystems
