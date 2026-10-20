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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.Ico0_inj
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.a_rel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.mkElement_mem

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise811

open NeighborhoodSystem ApproximableMap

/-- Any `R`-neighbourhood `[0,s)` forces `0 < s ≤ 1` (even though `R_mem_iff` phrases `R.mem X` as
an existential over a *possibly different* endpoint, injectivity pins it down to `s` itself). -/
theorem R_mem_Ico0 {s : ℚ} (h : R.mem (Set.Ico (0 : ℚ) s)) : 0 < s ∧ s ≤ 1 := by
  obtain ⟨r, hr0, hr1, heq⟩ := h
  have hsne : (Set.Ico (0 : ℚ) s).Nonempty := heq ▸ ⟨0, le_refl 0, hr0⟩
  obtain ⟨x, hx0, hxs⟩ := hsne
  have hs0 : 0 < s := lt_of_le_of_lt hx0 hxs
  have hsr : s = r := Ico0_inj hs0 hr0 heq
  exact ⟨hs0, hsr ▸ hr1⟩

end DomainTheory.NeighbourhoodSystems.Exercise811
