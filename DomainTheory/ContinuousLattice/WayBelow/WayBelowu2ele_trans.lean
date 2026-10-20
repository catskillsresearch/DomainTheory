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




/-- **Scott 1972, Proposition 2.2(iv).** `x ≤ y` and `y ≪ z` imply `x ≪ z` (monotone on the
left). -/
theorem WayBelow.le_trans {x y z : D} (hxy : x ≤ y) (h : y ≪ z) : x ≪ z := by
  obtain ⟨U, hU, hzU, hsub⟩ := h
  refine ⟨U, hU, hzU, fun w hw => ?_⟩
  have hyw : y ≤ w := Set.mem_Ici.1 (hsub hw)
  exact Set.mem_Ici.2 (hxy.trans hyw)

end DomainTheory.ContinuousLattice
