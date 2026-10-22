module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_9
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_10
public import DomainTheory.DataTypesAsLattices.Closures.boxShift_isRetract
public import DomainTheory.DataTypesAsLattices.Closures.boxShift_app_ne_bot
public import DomainTheory.DataTypesAsLattices.Closures.boxPlus_app_left
public import DomainTheory.DataTypesAsLattices.Closures.boxPlus_app_right
public import DomainTheory.DataTypesAsLattices.Closures.boxPlus_app_mixed
public import DomainTheory.DataTypesAsLattices.Closures.boxPlus_app_empty
public import DomainTheory.DataTypesAsLattices.Closures.boxPlus_app_bot
public import DomainTheory.DataTypesAsLattices.Closures.boxPlus_app_top

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem boxPlus_app_app {a b : Pomega} (ha : Retract a) (hb : Retract b)
    (u : Pomega) :
    funOf (boxPlus a b) (funOf (boxPlus a b) u) = funOf (boxPlus a b) u := by
  by_cases hx : squareFst u = botElem <;> by_cases hy : squareSnd u = botElem
  · rw [boxPlus_app_empty hx hy, boxPlus_app_bot]
  · rw [boxPlus_app_right hx hy,
      boxPlus_app_right (u := squarePair botElem (funOf (boxShift b) (squareSnd u)))
        (eq_5_9 _ _) (by rw [eq_5_10]; exact boxShift_app_ne_bot b _),
      eq_5_10, retract_app (boxShift_isRetract hb)]
  · rw [boxPlus_app_left hx hy,
      boxPlus_app_left (u := squarePair (funOf (boxShift a) (squareFst u)) botElem)
        (by rw [eq_5_9]; exact boxShift_app_ne_bot a _) (eq_5_10 _ _),
      eq_5_9, retract_app (boxShift_isRetract ha)]
  · rw [boxPlus_app_mixed hx hy, boxPlus_app_top]

end DomainTheory.DataTypesAsLattices
