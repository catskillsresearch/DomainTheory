module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62.instLeftCommutativeMkLeftInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62.instLeftCommutativeMkRightInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62.ProdCon_empty
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62.entSet_fst_of_prodEntSet

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β)

namespace ApproximableMap

variable {C : InfoSys γ}

/-- **Proposition 6.2(1).** Approximable first projection. -/
def fstMap : ApproximableMap (productSystem A B) A where
  rel u v := u ∈ (productSystem A B).Con ∧ v ∈ A.Con ∧ A.EntSet (fstFinset A B u) v
  rel_dom h := h.1
  rel_cod h := h.2.1
  empty_rel := ⟨ProdCon_empty A B, A.con_empty, by
    rw [fstFinset_empty]; exact A.entSet_empty ∅⟩
  union_right := by
    rintro u v v' ⟨hu, hv, huv⟩ ⟨_, hv', huv'⟩
    have hEnt : A.EntSet (fstFinset A B u) (v ∪' v') :=
      proposition_2_3_vi (sys := A) huv huv'
    have hBig : fstFinset A B u ∪' (v ∪' v') ∈ A.Con :=
      proposition_2_3_ii (sys := A) hu.1 hEnt
    have hCon : v ∪' v' ∈ A.Con :=
      A.con_subset hBig (subset_funion_right _ _)
    exact ⟨hu, hCon, hEnt⟩
  mono := by
    rintro u u' v v' ⟨hu, hv, huv⟩ hEntu hEntv hu' hv'
    refine ⟨hu', hv', ?_⟩
    exact proposition_2_3_iv A hu'.1 hv
      (proposition_2_3_iv A hu'.1 hu.1 (entSet_fst_of_prodEntSet A B hEntu) huv) hEntv

end ApproximableMap

end InfoSys

end DomainTheory.InformationSystems
