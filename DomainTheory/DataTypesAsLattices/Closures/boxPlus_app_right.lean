/-ai
Occupancy test of (5.13). If the left square component of u is empty and the right component is inhabited, applying the boxed sum of a and b to u yields the square pair of the empty set with the shifted application of b to the right component.

A member of the right component makes its occupancy tag the singleton one. The left tag is empty, the union is that singleton, and the double conditional of the one tag selects the right branch.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.botElem_union
public import DomainTheory.DataTypesAsLattices.Closures.exists_mem_of_ne_bot
public import DomainTheory.DataTypesAsLattices.Closures.boxTag_bot
public import DomainTheory.DataTypesAsLattices.Closures.boxTag_of_mem
public import DomainTheory.DataTypesAsLattices.Closures.boxPlus_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- Occupancy test of (5.13): only the right component is inhabited. -/
theorem boxPlus_app_right {a b u : Pomega} (hx : squareFst u = botElem)
    (hy : squareSnd u ≠ botElem) :
    funOf (boxPlus a b) u =
      squarePair botElem (funOf (boxShift b) (squareSnd u)) := by
  obtain ⟨m, hm⟩ := exists_mem_of_ne_bot hy
  rw [boxPlus_app, boxTag_of_mem hm, hx, boxTag_bot, botElem_union,
    dcondSet_ofNat_one]

end DomainTheory.DataTypesAsLattices
