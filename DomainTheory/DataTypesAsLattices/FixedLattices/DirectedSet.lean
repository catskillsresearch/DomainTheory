module

public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Data.Finset.Basic

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- A nonempty directed subset of a preorder. -/
class DirectedSet {α : Type u} [Preorder α] (s : Set α) : Prop where
  out : s.Nonempty ∧
    ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s →
      ∃ z ∈ s, x ≤ z ∧ y ≤ z

end DomainTheory.DataTypesAsLattices
