/-ai
In a linear order, any two upper sets are nested.

Case on whether the first upper set is contained in the second. If it is, that is the left alternative. If the containment fails, some token lies in the first set and fails to lie in the second. For a token of the second set, compare the two tokens. If the chosen token lies below the second token, the upper-set law of the first set puts the second token in the first set. If the second token lies below the chosen token, the upper-set law of the second set puts the chosen token in the second set, contradicting the choice.
ai-/
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
