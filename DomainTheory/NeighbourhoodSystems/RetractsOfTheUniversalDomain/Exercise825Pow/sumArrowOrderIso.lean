/-ai
The pointwise order on functions from a sum type is order-isomorphic to the product order on the two restricted function types. The forward map splits a family into its two summand restrictions, and the inverse joins a pair of families by the sum eliminator. The left round trip is extensionality by cases on the sum, and the right round trip is reflexivity. A pointwise inequality corresponds to the two restricted inequalities, by cases on the sum in one direction and by evaluation at the two inclusions in the other.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import Mathlib.Logic.Equiv.Nat

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

/-- The pointwise order on `α ⊕ β → E` corresponds, coordinatewise, to the product order on
`(α → E) × (β → E)`: splitting a sum-indexed family into its two summand-indexed restrictions is an
order isomorphism. -/
def sumArrowOrderIso (α β : Type*) (E : Type*) [Preorder E] :
    (α ⊕ β → E) ≃o (α → E) × (β → E) where
  toFun f := (fun a => f (Sum.inl a), fun b => f (Sum.inr b))
  invFun p := Sum.elim p.1 p.2
  left_inv f := by funext i; cases i <;> rfl
  right_inv p := rfl
  map_rel_iff' := by
    intro f g
    constructor
    · rintro ⟨h1, h2⟩ i
      cases i with
      | inl a => exact h1 a
      | inr b => exact h2 b
    · intro h
      exact ⟨fun a => h (Sum.inl a), fun b => h (Sum.inr b)⟩

end DomainTheory.NeighbourhoodSystems
