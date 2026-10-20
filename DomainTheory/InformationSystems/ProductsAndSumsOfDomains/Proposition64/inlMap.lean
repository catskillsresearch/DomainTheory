/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.instLeftCommutativeLiftSumLeft
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.instLeftCommutativeLiftSumRight
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.rht_eq_empty_of_sumEntSet
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.entSet_lft_of_sumEntSet
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.lft_mem_Con_of_SumCon_rht_empty

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β)

set_option linter.unusedSectionVars false

namespace ApproximableMap

variable {C : InfoSys γ}

/-- **Proposition 6.4(1).** Left injection. -/
def inlMap : ApproximableMap A (sumSystem A B) where
  rel v u := v ∈ A.Con ∧ SumCon A B u ∧ rhtFinset u = ∅ ∧ A.EntSet v (lftFinset u)
  rel_dom h := h.1
  rel_cod h := h.2.1
  empty_rel := ⟨A.con_empty, SumCon_empty A B, by rw [rhtFinset_empty], A.entSet_empty ∅⟩
  union_right := by
    rintro v u u' ⟨hv, hu, hr, hEnt⟩ ⟨_, hu', hr', hEnt'⟩
    refine ⟨hv, ?_, ?_, ?_⟩
    · have hl : lftFinset (u ∪' u') ∈ A.Con := by
        rw [lftFinset_funion]
        exact A.con_subset
          (proposition_2_3_ii (sys := A) hv (proposition_2_3_vi (sys := A) hEnt hEnt'))
          (subset_funion_right _ _)
      exact Or.inl ⟨hl, by rw [rhtFinset_funion, hr, hr']; rfl⟩
    · rw [rhtFinset_funion, hr, hr']; rfl
    · rw [lftFinset_funion]; exact proposition_2_3_vi (sys := A) hEnt hEnt'
  mono := by
    rintro v v' u u' ⟨hv, hu, hr, hEnt⟩ hEntv hEntu hv' hu'
    refine ⟨hv', hu', rht_eq_empty_of_sumEntSet A B hr hEntu, ?_⟩
    exact proposition_2_3_iv (sys := A) hv'
      (lft_mem_Con_of_SumCon_rht_empty A B hu hr)
      (proposition_2_3_iv (sys := A) hv' hv hEntv hEnt)
      (entSet_lft_of_sumEntSet A B hEntu)

end ApproximableMap

end InfoSys

end DomainTheory.InformationSystems
