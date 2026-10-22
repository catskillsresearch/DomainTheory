/-ai
Occupancy test of (5.13). If both square components of u are empty, applying the boxed sum of a and b to u yields the empty set.

The application unfolds, both occupancy tags of the empty set are empty, their union is empty, and the double conditional of the empty test is empty.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.boxTag_bot
public import DomainTheory.DataTypesAsLattices.Closures.boxPlus_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- Occupancy test of (5.13): neither component inhabited, so the value is `⊥`. -/
theorem boxPlus_app_empty {a b u : Pomega} (hx : squareFst u = botElem)
    (hy : squareSnd u = botElem) :
    funOf (boxPlus a b) u = botElem := by
  rw [boxPlus_app, hx, hy, boxTag_bot, boxTag_bot, Set.union_self, dcondSet_bot]

end DomainTheory.DataTypesAsLattices
