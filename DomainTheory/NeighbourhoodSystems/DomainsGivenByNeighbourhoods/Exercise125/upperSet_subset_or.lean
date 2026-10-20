module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Order.UpperLower.Basic
import all Mathlib.Order.UpperLower.Basic
public import Mathlib.Order.Bounds.Basic
import all Mathlib.Order.Bounds.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace FinalSegment

open NeighborhoodSystem

/-- In a linear order, any two upper sets are nested. (Hence final segments are
*nested-or-disjoint* — in fact always nested.) -/
theorem upperSet_subset_or {Δ : Type*} [LinearOrder Δ] {X Y : Set Δ}
    (hX : IsUpperSet X) (hY : IsUpperSet Y) : X ⊆ Y ∨ Y ⊆ X := by
  by_cases h : X ⊆ Y
  · exact Or.inl h
  · right
    rw [Set.not_subset] at h
    obtain ⟨a, haX, haY⟩ := h
    intro b hbY
    rcases le_total a b with hab | hba
    · exact hX hab haX
    · exact absurd (hY hba hbY) haY

end FinalSegment

end DomainTheory.NeighbourhoodSystems
