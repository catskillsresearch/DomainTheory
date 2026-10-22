module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.instLeftCommutativeLiftSumLeft
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.instLeftCommutativeLiftSumRight
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.lft_eq_empty_of_sumEntSet
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.entSet_rht_of_sumEntSet
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.rht_mem_Con_of_SumCon_lft_empty

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β)

namespace ApproximableMap

variable {C : InfoSys γ}

/-- **Proposition 6.4(2).** Right injection. -/
def inrMap : ApproximableMap B (sumSystem A B) where
  rel w u := w ∈ B.Con ∧ SumCon A B u ∧ lftFinset u = ∅ ∧ B.EntSet w (rhtFinset u)
  rel_dom h := h.1
  rel_cod h := h.2.1
  empty_rel := ⟨B.con_empty, SumCon_empty A B, by rw [lftFinset_empty], B.entSet_empty ∅⟩
  union_right := by
    rintro w u u' ⟨hw, hu, hl, hEnt⟩ ⟨_, hu', hl', hEnt'⟩
    refine ⟨hw, ?_, ?_, ?_⟩
    · have hrC : rhtFinset (u ∪' u') ∈ B.Con := by
        rw [rhtFinset_funion]
        exact B.con_subset
          (proposition_2_3_ii (sys := B) hw (proposition_2_3_vi (sys := B) hEnt hEnt'))
          (subset_funion_right _ _)
      exact Or.inr ⟨by rw [lftFinset_funion, hl, hl']; rfl, hrC⟩
    · rw [lftFinset_funion, hl, hl']; rfl
    · rw [rhtFinset_funion]; exact proposition_2_3_vi (sys := B) hEnt hEnt'
  mono := by
    rintro w w' u u' ⟨hw, hu, hl, hEnt⟩ hEntw hEntu hw' hu'
    refine ⟨hw', hu', lft_eq_empty_of_sumEntSet A B hl hEntu, ?_⟩
    exact proposition_2_3_iv (sys := B) hw'
      (rht_mem_Con_of_SumCon_lft_empty A B hu hl)
      (proposition_2_3_iv (sys := B) hw' hw hEntw hEnt)
      (entSet_rht_of_sumEntSet A B hEntu)

end ApproximableMap

end InfoSys

end DomainTheory.InformationSystems
