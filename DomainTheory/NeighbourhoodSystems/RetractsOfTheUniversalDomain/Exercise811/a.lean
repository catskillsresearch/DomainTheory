/-ai
Exercise 8.11's approximable map a from R to R is the map whose relation is Scott's relation on half-open intervals. Related sets are R-neighbourhoods, the master is related to itself by the endpoint clause r = s = 1, outputs are closed under intersection by the endpoint form of that clause, and the relation is monotone by comparing endpoints of nested intervals.
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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.Ico0_inj
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.Ico0_le_of_subset
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.aRel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.aRel_combine

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise811

open NeighborhoodSystem ApproximableMap

/-- **Exercise 8.11 (first part).** `aRel` defines an approximable map `a : R → R`. -/
def a : ApproximableMap R R where
  rel := aRel
  rel_dom := fun ⟨r, _, hr0, hr1, _, _, hXr, _, _⟩ => ⟨r, hr0, hr1, hXr⟩
  rel_cod := fun ⟨_, s, _, _, hs0, hs1, _, hYs, _⟩ => ⟨s, hs0, hs1, hYs⟩
  master_rel := ⟨1, 1, one_pos, le_rfl, one_pos, le_rfl, rfl, rfl, Or.inr ⟨rfl, rfl⟩⟩
  inter_right := by
    rintro X Y Y' ⟨r, s, hr0, hr1, hs0, hs1, rfl, rfl, hcond⟩
      ⟨r', s', hr0', hr1', hs0', hs1', hXr', rfl, hcond'⟩
    have hrr' : r = r' := Ico0_inj hr0 hr0' hXr'
    subst hrr'
    rw [Set.Ico_inter_Ico, sup_idem]
    exact ⟨r, min s s', hr0, hr1, lt_min hs0 hs0', (min_le_left s s').trans hs1, rfl, rfl,
      aRel_combine hs1 hs1' hcond hcond'⟩
  mono := by
    rintro X X' Y Y' ⟨r, s, hr0, hr1, hs0, hs1, rfl, rfl, hcond⟩ hX'X hYY'
      ⟨r', hr0', hr1', rfl⟩ ⟨s', hs0', hs1', rfl⟩
    have hr'r : r' ≤ r := Ico0_le_of_subset hr0' hX'X
    have hss' : s ≤ s' := Ico0_le_of_subset hs0 hYY'
    refine ⟨r', s', hr0', hr1', hs0', hs1', rfl, rfl, ?_⟩
    rcases hcond with hlt | ⟨rfl, rfl⟩
    · exact Or.inl (hr'r.trans_lt (hlt.trans_le hss'))
    · rcases hr1'.lt_or_eq with h | h
      · exact Or.inl (h.trans_le hss')
      · exact Or.inr ⟨h, le_antisymm hs1' hss'⟩

end DomainTheory.NeighbourhoodSystems.Exercise811
