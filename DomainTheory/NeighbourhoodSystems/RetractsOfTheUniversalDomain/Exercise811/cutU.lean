/-ai
The Dedekind up-set of a real t at a rational r holds when r ≤ 1 and either the cut point 1 − t is strictly less than r, or r = 1. The cut point is chosen so that the represented real increases exactly as the up-set does.
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

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise811

open NeighborhoodSystem ApproximableMap

/-- **The Dedekind-cut up-set for `t ∈ [0,1]`.** `cutU t r` holds at `r ≤ 1` with `1 - t < r`
(strictly), or at the single endpoint `r = 1`; `1 - t` is Scott's "cut point" `c`, chosen so the
represented real `t` increases exactly as the up-set does (Scott's hint: `⊆` matches `≤`). -/
def cutU (t : ℝ) (r : ℚ) : Prop := r ≤ 1 ∧ ((1 - t : ℝ) < (r : ℝ) ∨ r = 1)

end DomainTheory.NeighbourhoodSystems.Exercise811
