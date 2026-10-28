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
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.not_mem_right_of_mem_left
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.sumElementRht

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β)

namespace ApproximableMap

variable {C : InfoSys γ}

def inrMap : ApproximableMap B (sumSystem A B) where
  rel w u := w ∈ B.Con ∧ SumCon A B u ∧ lftFinset u = ∅ ∧ B.EntSet w (rhtFinset u)
  rel_dom h := h.1
  rel_cod h := h.2.1
  empty_rel := ⟨B.con_empty, SumCon_empty A B, by rw [lftFinset.empty], B.entSet_empty ∅⟩
  union_right := by
    rintro w u u' ⟨hw, hu, hl, hEnt⟩ ⟨_, hu', hl', hEnt'⟩
    refine ⟨hw, ?_, ?_, ?_⟩
    · have hrC : rhtFinset (u ∪' u') ∈ B.Con := by
        rw [rhtFinset.funion]
        exact B.con_subset
          (proposition_2_3_ii (sys := B) hw (proposition_2_3_vi (sys := B) hEnt hEnt'))
          (subset_funion_right _ _)
      exact Or.inr ⟨by rw [lftFinset.funion, hl, hl']; rfl, hrC⟩
    · rw [lftFinset.funion, hl, hl']; rfl
    · rw [rhtFinset.funion]; exact proposition_2_3_vi (sys := B) hEnt hEnt'
  mono := by
    rintro w w' u u' ⟨hw, hu, hl, hEnt⟩ hEntw hEntu hw' hu'
    refine ⟨hw', hu', lft_eq_empty_of_sumEntSet A B hl hEntu, ?_⟩
    exact proposition_2_3_iv (sys := B) hw'
      (rht_mem_Con_of_SumCon_lft_empty A B hu hl)
      (proposition_2_3_iv (sys := B) hw' hw hEntw hEnt)
      (entSet_rht_of_sumEntSet A B hEntu)

theorem inrMap.toElement_sumElementRht (z : (sumSystem A B).Element)
    (y0 : β) (hy0 : SumToken.right y0 ∈ z.carrier) :
    (inrMap A B).toElement (sumElementRht A B z y0 hy0) = z := by
  apply le_antisymm
  · intro p ⟨w, hw, ⟨hwCon, huCon, hl, hEnt⟩⟩
    cases p with
    | bot => exact factoid_3_2 (sumSystem A B) z
    | right y =>
      have hEnty : B.Ent w y := by
        have : rhtFinset ({SumToken.right y} : Finset (SumToken α β)) = {y} :=
          rhtFinset.singleton_right y
        simpa [this] using hEnt y (Finset.mem_singleton_self y)
      exact (sumElementRht A B z y0 hy0).closed w y hw hEnty
    | left x =>
      have : lftFinset ({SumToken.left x} : Finset (SumToken α β)) = {x} :=
        lftFinset.singleton_left x
      exact False.elim (Finset.singleton_ne_empty x (this ▸ hl))
  · intro p hp
    cases p with
    | bot =>
      refine ⟨∅, fun _ h => False.elim (Finset.notMem_empty _ (Finset.mem_coe.1 h)), ?_⟩
      exact ⟨B.con_empty, (sumSystem A B).con_sing _, by rw [lftFinset.singleton_bot],
        B.entSet_empty _⟩
    | right y =>
      refine ⟨{y}, ?_, ?_⟩
      · intro b hb
        have : b = y := Finset.mem_singleton.mp (Finset.mem_coe.1 hb)
        subst this; exact hp
      · refine ⟨B.con_sing y, (sumSystem A B).con_sing _, ?_, ?_⟩
        · ext x; constructor
          · intro hx
            have : SumToken.left x ∈ ({SumToken.right y} : Finset _) := (mem_lftFinset).1 hx
            exact False.elim (nomatch Finset.mem_singleton.mp this)
          · intro hx; exact False.elim (Finset.notMem_empty x hx)
        · rw [rhtFinset.singleton_right]
          exact proposition_2_3_iii B (B.con_sing y)
    | left x =>
      exact False.elim (not_mem_right_of_mem_left A B z hp hy0)

end ApproximableMap

end InfoSys

end DomainTheory.InformationSystems
