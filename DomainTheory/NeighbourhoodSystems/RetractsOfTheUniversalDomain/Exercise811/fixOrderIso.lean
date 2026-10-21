/-ai
The fixed points of the approximable map a on R are order-isomorphic to the closed unit interval of real numbers. A fixed point is sent to its cut point, which lies between 0 and 1, and a real t in that interval is sent to the cut element of t, which is fixed by a. These maps invert one another because a fixed point equals the cut element of its cut point, and because cut elements are injective once the cut element of t is recovered from the cut point of that fixed cut element. One cut point is at most another exactly when the corresponding elements are ordered that way, by the order criterion for cut elements rewritten along those recovery identities.
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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.R
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.R_mem_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.R_master
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.a
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.a_rel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.mkElement_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.cutElt
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.cutElt_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.toElementMap_cutElt
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.cutElt_le_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.cutPoint
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.cutPoint_nonneg
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.cutPoint_le_one
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.cutElt_cutPoint
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.cutElt_injective

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise811

open NeighborhoodSystem ApproximableMap

/-- **Exercise 8.11 (Dedekind-cut correspondence).** The fixed-point set of `a` is order
isomorphic to `Set.Icc (0 : ℝ) 1` — a one-one correspondence with the reals between `0` and `1`
inclusive, under which `⊆` (domain order) matches `≤` (Scott's hint). -/
noncomputable def fixOrderIso : {y : R.Element // a.toElementMap y = y} ≃o Set.Icc (0 : ℝ) 1 where
  toFun y := ⟨cutPoint y.1, cutPoint_nonneg y.1, cutPoint_le_one y.1⟩
  invFun t := ⟨cutElt t.1 t.2.2, toElementMap_cutElt t.2.2⟩
  left_inv y := Subtype.ext (cutElt_cutPoint y.2)
  right_inv t := Subtype.ext (cutElt_injective (cutPoint_nonneg _) (cutPoint_le_one _) t.2.1 t.2.2
    (cutElt_cutPoint (toElementMap_cutElt t.2.2)))
  map_rel_iff' := by
    intro y y'
    show cutPoint y.1 ≤ cutPoint y'.1 ↔ y.1 ≤ y'.1
    constructor
    · intro h
      have h' := (cutElt_le_iff (cutPoint_nonneg y.1) (cutPoint_le_one y.1) (cutPoint_nonneg y'.1)
        (cutPoint_le_one y'.1)).mpr h
      rwa [cutElt_cutPoint y.2, cutElt_cutPoint y'.2] at h'
    · intro h
      rw [← cutElt_cutPoint y.2, ← cutElt_cutPoint y'.2] at h
      exact (cutElt_le_iff (cutPoint_nonneg y.1) (cutPoint_le_one y.1) (cutPoint_nonneg y'.1)
        (cutPoint_le_one y'.1)).mp h

end DomainTheory.NeighbourhoodSystems.Exercise811
