/-ai
The Dedekind up-set is monotone in the real: if t ≤ t' and the up-set of t holds at r, then the up-set of t' holds at r. Raising t weakens the cut point 1 − t and enlarges the up-set.

The bound r ≤ 1 is kept. If 1 − t is strictly below r, then 1 − t' is strictly below r as well. If r = 1, that alternative is kept.
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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.cutElt_mem

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise811

open NeighborhoodSystem ApproximableMap

/-- `cutU` is monotone in `t`: raising `t` only weakens the cut point `1 - t`, so it only
*enlarges* the up-set. -/
theorem cutU_mono {t t' : ℝ} (htt' : t ≤ t') {r : ℚ} (h : cutU t r) : cutU t' r := by
  refine ⟨h.1, ?_⟩
  rcases h.2 with hc | rfl
  · exact Or.inl (by linarith)
  · exact Or.inr rfl

end DomainTheory.NeighbourhoodSystems.Exercise811
