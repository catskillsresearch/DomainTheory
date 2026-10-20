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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.Ico0_inj
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.a_rel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.mkElement_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.cutU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.cutU_pos
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.cutElt

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise811

open NeighborhoodSystem ApproximableMap

@[simp] theorem cutElt_mem {t : ℝ} {ht1 : t ≤ 1} {r : ℚ} :
    (cutElt t ht1).mem (Set.Ico 0 r) ↔ cutU t r := by
  simp only [cutElt, mkElement_mem]
  constructor
  · rintro ⟨r', hr', heq⟩
    have hr'0 := cutU_pos ht1 hr'
    have hne : (Set.Ico (0 : ℚ) r).Nonempty := heq ▸ ⟨0, le_refl 0, hr'0⟩
    obtain ⟨x, hx0, hxr⟩ := hne
    have hr0 : 0 < r := lt_of_le_of_lt hx0 hxr
    rwa [Ico0_inj hr0 hr'0 heq]
  · exact fun h => ⟨r, h, rfl⟩

end DomainTheory.NeighbourhoodSystems.Exercise811
