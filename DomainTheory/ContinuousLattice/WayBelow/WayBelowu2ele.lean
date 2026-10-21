/-ai
Scott 1972, Proposition 2.2(v). If x is way below y, then x lies below y.

The witnessing Scott-open neighbourhood of y is contained in the principal upset of x, so y lies in that upset.
ai-/
module

public import Mathlib.Order.CompleteLattice.Basic
import all Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.UpperLower.Basic
import all Mathlib.Order.UpperLower.Basic
public import Mathlib.Order.Directed
import all Mathlib.Order.Directed
public import DomainTheory.ContinuousLattice.WayBelow.Basic

@[expose] public section


namespace DomainTheory.ContinuousLattice

universe u

variable {D : Type u} [CompleteLattice D]


/-- **Scott 1972, Proposition 2.2(v).** `x ≪ y` implies `x ≤ y`. -/
theorem WayBelow.le {x y : D} (h : x ≪ y) : x ≤ y := by
  obtain ⟨U, _, hyU, hsub⟩ := h
  exact hsub hyU

end DomainTheory.ContinuousLattice
