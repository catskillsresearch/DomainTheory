module

public import Mathlib.Order.CompleteLattice.Defs
import all Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Data.Finset.Basic
import all Mathlib.Data.Finset.Basic

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- A nonempty directed subset of a preorder. -/
def IsDirectedSet {α : Type u} [Preorder α] (s : Set α) : Prop :=
  s.Nonempty ∧
    ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s →
      ∃ z ∈ s, x ≤ z ∧ y ≤ z

end DomainTheory.DataTypesAsLattices
