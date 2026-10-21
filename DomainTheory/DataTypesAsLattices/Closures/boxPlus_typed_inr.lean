/-ai
Scott 1976, Theorem 5.4, the analogue of (4.5). If y is a fixed value of the shift of b, the right square pair of the empty set with y is a fixed value of the boxed sum of a and b.

The shifted application is never empty, so y is nonempty. The right occupancy case, together with the square-projection equations, returns the square pair of the empty set with y once the typing equation for y is cancelled.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_9
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_10
public import DomainTheory.DataTypesAsLattices.Closures.boxShift_app_ne_bot
public import DomainTheory.DataTypesAsLattices.Closures.boxPlus_app_right

@[expose] public section


namespace DomainTheory.DataTypesAsLattices































/-- **Scott 1976, Theorem 5.4 / analogue of 4.5.** Right injection into the
paper sum, on the shifted summand. -/
theorem boxPlus_typed_inr {a b y : Pomega} (hy : typed y (boxShift b)) :
    typed (squarePair botElem y) (boxPlus a b) := by
  have hy0 : y ≠ botElem := by
    rw [hy]; exact boxShift_app_ne_bot b y
  rw [typed, boxPlus_app_right (eq_5_9 _ _) (by rw [eq_5_10]; exact hy0), eq_5_10,
    ← hy]

end DomainTheory.DataTypesAsLattices
