/-ai
If t is at most 1 and a rational r lies in the cut up-set cutU t, then r is positive.

The second clause of membership is either the strict inequality 1 − t < r, or the equality r = 1. In the first case t ≤ 1 gives 0 ≤ 1 − t, and casting that bound yields 0 < r. In the second case r = 1 is positive.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import Mathlib.Data.Rat.Cast.Order
import all Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.Order.Archimedean.Basic
import all Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Order.Bounds.OrderIso
import all Mathlib.Order.Bounds.OrderIso
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
import all Mathlib.Order.ConditionallyCompleteLattice.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.R_mem_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.R_master
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.a_rel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.mkElement_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.cutU

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise811

open NeighborhoodSystem ApproximableMap

theorem cutU_pos {t : ℝ} (ht1 : t ≤ 1) {r : ℚ} (h : cutU t r) : 0 < r := by
  rcases h.2 with h2 | rfl
  · have hc : (0 : ℝ) ≤ 1 - t := by linarith
    exact_mod_cast lt_of_le_of_lt hc h2
  · norm_num

end DomainTheory.NeighbourhoodSystems.Exercise811
