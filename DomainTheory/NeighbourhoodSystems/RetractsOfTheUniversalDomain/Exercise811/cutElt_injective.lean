/-ai
The cut element is injective on the unit interval.

The order characterization supplies both inequalities between the two reals, and antisymmetry gives equality.
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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.cutElt
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.cutElt_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.cutElt_le_iff

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise811

open NeighborhoodSystem ApproximableMap

/-- `cutElt` is injective on `[0,1]` (antisymmetry of `cutElt_le_iff`). -/
theorem cutElt_injective {t t' : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (ht0' : 0 ≤ t') (ht1' : t' ≤ 1)
    (h : cutElt t ht1 = cutElt t' ht1') : t = t' :=
  le_antisymm ((cutElt_le_iff ht0 ht1 ht0' ht1').mp h.le) ((cutElt_le_iff ht0' ht1' ht0 ht1).mp h.ge)

end DomainTheory.NeighbourhoodSystems.Exercise811
