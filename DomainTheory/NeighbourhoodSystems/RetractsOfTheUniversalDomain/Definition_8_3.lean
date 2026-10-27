module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition_8_2

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {D E : NeighborhoodSystem α}

/- concordance: source L4801 DEFINITION 8.3 projections -/
/-- **Definition 8.3, first clause (Scott 1981, PRG-19).** A retraction `a : E → E` is a
*projection* provided `a ⊑ I_E`. (We do not separately require `Retraction a` in the
definition, matching Scott's usage where "projection" is applied to a retraction already in
hand; the conjunction is spelled out where needed, e.g. `FinitaryProjection`.) -/
def IsProjection (a : ApproximableMap E E) : Prop := Retraction a ∧ a ≤ idMap E

/-- A **finitary projection**: both clauses of Definition 8.3 together with `Retraction`. -/
class FinitaryProjection (a : ApproximableMap E E) : Prop where
  out : IsProjection a ∧ IsFinitary a

end

section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {D E : NeighborhoodSystem α}

namespace Subsystem

variable {h : D ◁ E}

/-- **Every `retractionOfSubsystem h` is finitary** (Definition 8.3): its fixed-point set is
isomorphic to `|D|` itself, by Proposition 8.2's `elementIso`. -/
theorem isFinitary_retractionOfSubsystem (h : D ◁ E) :
    IsFinitary (retractionOfSubsystem h) :=
  ⟨α, D, ⟨(elementIso h).symm⟩⟩

/-- **Scott's remark before Definition 8.3.** Every retraction `a = retractionOfSubsystem h` of
Proposition 8.2 satisfies `a ⊑ I_E`: unwinding `X a Z ↔ ∃ Y ∈ D, X ⊆ Y ⊆ Z` gives `X ⊆ Z`
directly. -/
theorem retractionOfSubsystem_le_idMap (h : D ◁ E) : retractionOfSubsystem h ≤ idMap E := by
  intro X Z hr
  obtain ⟨hEX, hEZ, Y, _, hXY, hYZ⟩ := (retractionOfSubsystem_rel h).mp hr
  exact ⟨hEX, hEZ, hXY.trans hYZ⟩

/-- **Every `retractionOfSubsystem h` is a projection** (Definition 8.3). -/
theorem isProjection_retractionOfSubsystem (h : D ◁ E) :
    IsProjection (retractionOfSubsystem h) :=
  ⟨isRetraction_retractionOfSubsystem h, retractionOfSubsystem_le_idMap h⟩

/-- **Every `retractionOfSubsystem h` is a finitary projection** (Definition 8.3, both clauses). -/
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
