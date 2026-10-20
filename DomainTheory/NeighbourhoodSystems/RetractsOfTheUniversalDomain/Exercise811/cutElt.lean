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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.R
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.R_mem_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.R_master
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.a_rel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.mkElement
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.mkElement_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.cutU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.cutU_pos
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.cutU_le1
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.cutU_one
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.cutU_up

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise811

open NeighborhoodSystem ApproximableMap

/-- The fixed point of `a` corresponding to `t ∈ [0,1]` (Scott's Dedekind cut). -/
def cutElt (t : ℝ) (ht1 : t ≤ 1) : R.Element :=
  mkElement (cutU t) cutU_one (fun _ h => cutU_pos ht1 h) (fun _ h => cutU_le1 h)
    (fun _ _ h hrs hs1 => cutU_up h hrs hs1)

end DomainTheory.NeighbourhoodSystems.Exercise811
