/-ai
Scott 1976, Theorem 5.4, the analogue of (4.5). If x is a fixed value of the shift of a, the left square pair of x with the empty set is a fixed value of the boxed sum of a and b.

The shifted application is never empty, so x is nonempty. The left occupancy case, together with the square-projection equations, returns the square pair of x with the empty set once the typing equation for x is cancelled.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_9
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_10
public import DomainTheory.DataTypesAsLattices.Closures.boxShift_app_ne_bot
public import DomainTheory.DataTypesAsLattices.Closures.boxPlus_app_left

@[expose] public section


namespace DomainTheory.DataTypesAsLattices































/-- **Scott 1976, Theorem 5.4 / analogue of 4.5.** Left injection into the
paper sum, on the shifted summand. -/
theorem boxPlus_typed_inl {a b x : Pomega} (hx : typed x (boxShift a)) :
    typed (squarePair x botElem) (boxPlus a b) := by
  have hx0 : x ≠ botElem := by
    rw [hx]; exact boxShift_app_ne_bot a x
  rw [typed, boxPlus_app_left (by rw [eq_5_9]; exact hx0) (eq_5_10 _ _), eq_5_9,
    ← hx]

end DomainTheory.DataTypesAsLattices
