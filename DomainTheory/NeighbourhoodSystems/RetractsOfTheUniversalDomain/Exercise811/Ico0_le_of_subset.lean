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

/-- If `[0,p) ⊆ [0,q)` and `p > 0`, then `p ≤ q`. (The converse direction of nestedness; note `q > 0`
is *derived*, from `0 ∈ [0,p) ⊆ [0,q)`, not assumed.) -/
theorem Ico0_le_of_subset {p q : ℚ} (hp : 0 < p)
    (hsub : Set.Ico (0 : ℚ) p ⊆ Set.Ico (0 : ℚ) q) : p ≤ q := by
  have hq : (0 : ℚ) < q := (hsub ⟨le_refl 0, hp⟩).2
  by_contra hlt
  rw [not_le] at hlt
  exact absurd (hsub ⟨hq.le, hlt⟩).2 (lt_irrefl q)

end DomainTheory.NeighbourhoodSystems.Exercise811
