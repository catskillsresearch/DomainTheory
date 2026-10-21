/-ai
Occupancy test of (5.13). If the left square component of u is inhabited and the right component is empty, applying the boxed sum of a and b to u yields the square pair of the shifted application of a to the left component with the empty set.

A member of the left component makes its occupancy tag the singleton zero. The right tag is empty, the union is that singleton, and the double conditional of the zero tag selects the left branch.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.union_botElem
public import DomainTheory.DataTypesAsLattices.Closures.exists_mem_of_ne_bot
public import DomainTheory.DataTypesAsLattices.Closures.boxTag_bot
public import DomainTheory.DataTypesAsLattices.Closures.boxTag_of_mem
public import DomainTheory.DataTypesAsLattices.Closures.boxPlus_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- Occupancy test of (5.13): only the left component is inhabited. -/
theorem boxPlus_app_left {a b u : Pomega} (hx : squareFst u ≠ botElem)
    (hy : squareSnd u = botElem) :
    funOf (boxPlus a b) u =
      squarePair (funOf (boxShift a) (squareFst u)) botElem := by
  obtain ⟨m, hm⟩ := exists_mem_of_ne_bot hx
  rw [boxPlus_app, boxTag_of_mem hm, hy, boxTag_bot, union_botElem,
    dcondSet_ofNat_zero]

end DomainTheory.DataTypesAsLattices
