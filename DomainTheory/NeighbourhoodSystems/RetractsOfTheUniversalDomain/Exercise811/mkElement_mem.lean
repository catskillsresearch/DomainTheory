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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.mkElement

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise811

open NeighborhoodSystem ApproximableMap

@[simp] theorem mkElement_mem {U hU1 hUpos hUle1 hUup} {X : Set ℚ} :
    (mkElement U hU1 hUpos hUle1 hUup).mem X ↔ ∃ r, U r ∧ X = Set.Ico (0 : ℚ) r := Iff.rfl

end DomainTheory.NeighbourhoodSystems.Exercise811
