module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition_8_2

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {D E : NeighborhoodSystem α}

def IsProjection (a : ApproximableMap E E) : Prop := Retraction a ∧ a ≤ idMap E

class FinitaryProjection (a : ApproximableMap E E) : Prop where
  out : IsProjection a ∧ IsFinitary a

end

section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {D E : NeighborhoodSystem α}

namespace Subsystem

variable {h : D ◁ E}

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
end

open NeighborhoodSystem ApproximableMap ApproximableMap₂

theorem fin2_zero_ne_zero_one : ({0} : Set (Fin 2)) ≠ ({0, 1} : Set (Fin 2)) := by
  intro h
  have h1 : (1 : Fin 2) ∈ ({0, 1} : Set (Fin 2)) := by simp
  rw [← h] at h1
  simp at h1

theorem fin2_zero_subset_zero_one : ({0} : Set (Fin 2)) ⊆ ({0, 1} : Set (Fin 2)) := by
  intro x hx; simp only [Set.mem_singleton_iff] at hx; subst hx; simp

end DomainTheory.NeighbourhoodSystems
