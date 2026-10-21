/-ai
The left injection of Proposition 6.4 is the approximable map from A to the separated sum that relates a consistent set v of A to a sum-consistent set u whose right projection is empty exactly when A entails the left projection of u from v. The domain and codomain of a related pair are the two consistency hypotheses. The empty relation holds because both empty sets are consistent, the right projection of the empty sum set is empty, and A entails the empty set from the empty set. Closure under union on the right uses proposition 2.3(vi) for the entailments, proposition 2.3(ii) and the subset axiom for consistency of the union of the left projections, and emptiness of both right projections to obtain emptiness of the right projection of the union, which is the left disjunct of sum consistency. Monotonicity keeps the right projection empty by the entailment lemma, and combines the two entailments by two applications of proposition 2.3(iv), using consistency of the left projection when the right projection is empty.
ai-/
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
