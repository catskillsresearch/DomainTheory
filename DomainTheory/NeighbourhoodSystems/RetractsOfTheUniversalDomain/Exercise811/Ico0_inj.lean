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

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise811

open NeighborhoodSystem ApproximableMap

/-- The parametrization `r ↦ [0,r)` is injective on positive `r`: if `r < s` then `r` itself
witnesses the difference (`r ∈ [0,s)` but `r ∉ [0,r)`). -/
theorem Ico0_inj {r s : ℚ} (hr : 0 < r) (hs : 0 < s)
    (h : Set.Ico (0 : ℚ) r = Set.Ico (0 : ℚ) s) : r = s := by
  rcases lt_trichotomy r s with hlt | heq | hgt
  · have hmem : r ∈ Set.Ico (0 : ℚ) s := ⟨hr.le, hlt⟩
    rw [← h] at hmem
    exact absurd hmem.2 (lt_irrefl r)
  · exact heq
  · have hmem : s ∈ Set.Ico (0 : ℚ) r := ⟨hs.le, hgt⟩
    rw [h] at hmem
    exact absurd hmem.2 (lt_irrefl s)

end DomainTheory.NeighbourhoodSystems.Exercise811
