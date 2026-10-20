module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62.instLeftCommutativeMkLeftInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62.instLeftCommutativeMkRightInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62.ProdCon_empty
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62.entSet_snd_of_prodEntSet

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β)

namespace ApproximableMap

variable {C : InfoSys γ}

/-- **Proposition 6.2(2).** Approximable second projection. -/
def sndMap : ApproximableMap (productSystem A B) B where
  rel u w := u ∈ (productSystem A B).Con ∧ w ∈ B.Con ∧ B.EntSet (sndFinset A B u) w
  rel_dom h := h.1
  rel_cod h := h.2.1
  empty_rel := ⟨ProdCon_empty A B, B.con_empty, by
    rw [sndFinset_empty]; exact B.entSet_empty ∅⟩
  union_right := by
    rintro u w w' ⟨hu, hw, huw⟩ ⟨_, hw', huw'⟩
    have hEnt : B.EntSet (sndFinset A B u) (w ∪' w') :=
      proposition_2_3_vi (sys := B) huw huw'
    have hBig : sndFinset A B u ∪' (w ∪' w') ∈ B.Con :=
      proposition_2_3_ii (sys := B) hu.2 hEnt
    have hCon : w ∪' w' ∈ B.Con :=
      B.con_subset hBig (subset_funion_right _ _)
    exact ⟨hu, hCon, hEnt⟩
  mono := by
    rintro u u' w w' ⟨hu, hw, huw⟩ hEntu hEntw hu' hw'
    refine ⟨hu', hw', ?_⟩
    exact proposition_2_3_iv B hu'.2 hw
      (proposition_2_3_iv B hu'.2 hu.2 (entSet_snd_of_prodEntSet A B hEntu) huw) hEntw

end ApproximableMap

end InfoSys

end DomainTheory.InformationSystems
