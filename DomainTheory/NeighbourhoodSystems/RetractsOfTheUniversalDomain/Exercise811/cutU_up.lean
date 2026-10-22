module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Order.Bounds.OrderIso
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.R_mem_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.R_master
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.a_rel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.mkElement_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.cutU

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise811

open NeighborhoodSystem ApproximableMap

theorem cutU_up {r s : ℚ} {t : ℝ} (h : cutU t r) (hrs : r ≤ s) (hs1 : s ≤ 1) : cutU t s := by
  refine ⟨hs1, ?_⟩
  rcases h.2 with h2 | rfl
  · left
    have hcast : (r : ℝ) ≤ (s : ℝ) := by exact_mod_cast hrs
    linarith
  · exact Or.inr (le_antisymm hs1 hrs)

end DomainTheory.NeighbourhoodSystems.Exercise811
