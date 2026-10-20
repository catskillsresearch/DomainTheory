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
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.Basic
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.not_mem_right_of_mem_left

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β)

set_option linter.unusedSectionVars false



















namespace ApproximableMap

variable {C : InfoSys γ}









theorem inrMap_toElement_sumElementRht (z : (sumSystem A B).Element)
    (y0 : β) (hy0 : SumToken.right y0 ∈ z.carrier) :
    (inrMap A B).toElement (sumElementRht A B z y0 hy0) = z := by
  apply le_antisymm
  · intro p ⟨w, hw, ⟨hwCon, huCon, hl, hEnt⟩⟩
    cases p with
    | bot => exact factoid_3_2 (sumSystem A B) z
    | right y =>
      have hEnty : B.Ent w y := by
        have : rhtFinset ({SumToken.right y} : Finset (SumToken α β)) = {y} :=
          rhtFinset_singleton_right y
        simpa [this] using hEnt y (Finset.mem_singleton_self y)
      exact (sumElementRht A B z y0 hy0).closed w y hw hEnty
    | left x =>
      have : lftFinset ({SumToken.left x} : Finset (SumToken α β)) = {x} :=
        lftFinset_singleton_left x
      exact False.elim (Finset.singleton_ne_empty x (this ▸ hl))
  · intro p hp
    cases p with
    | bot =>
      refine ⟨∅, fun _ h => False.elim (Finset.notMem_empty _ (Finset.mem_coe.1 h)), ?_⟩
      exact ⟨B.con_empty, (sumSystem A B).con_sing _, by rw [lftFinset_singleton_bot],
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
        · rw [rhtFinset_singleton_right]
          exact proposition_2_3_iii B (B.con_sing y)
    | left x =>
      exact False.elim (not_mem_right_of_mem_left A B z hp hy0)

end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
