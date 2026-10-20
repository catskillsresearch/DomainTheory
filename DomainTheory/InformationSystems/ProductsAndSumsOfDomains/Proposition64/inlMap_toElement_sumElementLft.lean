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









theorem inlMap_toElement_sumElementLft (z : (sumSystem A B).Element)
    (x0 : α) (hx0 : SumToken.left x0 ∈ z.carrier) :
    (inlMap A B).toElement (sumElementLft A B z x0 hx0) = z := by
  apply le_antisymm
  · intro p ⟨v, hv, ⟨hvCon, huCon, hr, hEnt⟩⟩
    cases p with
    | bot => exact factoid_3_2 (sumSystem A B) z
    | left x =>
      have hEntx : A.Ent v x := by
        have : lftFinset ({SumToken.left x} : Finset (SumToken α β)) = {x} :=
          lftFinset_singleton_left x
        simpa [this] using hEnt x (Finset.mem_singleton_self x)
      exact (sumElementLft A B z x0 hx0).closed v x hv hEntx
    | right y =>
      have : rhtFinset ({SumToken.right y} : Finset (SumToken α β)) = {y} :=
        rhtFinset_singleton_right y
      exact False.elim (Finset.singleton_ne_empty y (this ▸ hr))
  · intro p hp
    cases p with
    | bot =>
      refine ⟨∅, fun _ h => False.elim (Finset.notMem_empty _ (Finset.mem_coe.1 h)), ?_⟩
      exact ⟨A.con_empty, (sumSystem A B).con_sing _, by rw [rhtFinset_singleton_bot],
        A.entSet_empty _⟩
    | left x =>
      refine ⟨{x}, ?_, ?_⟩
      · intro a ha
        have : a = x := Finset.mem_singleton.mp (Finset.mem_coe.1 ha)
        subst this; exact hp
      · refine ⟨A.con_sing x, (sumSystem A B).con_sing _, ?_, ?_⟩
        · ext y; constructor
          · intro hy
            have : SumToken.right y ∈ ({SumToken.left x} : Finset _) := (mem_rhtFinset).1 hy
            exact False.elim (nomatch Finset.mem_singleton.mp this)
          · intro hy; exact False.elim (Finset.notMem_empty y hy)
        · rw [lftFinset_singleton_left]
          exact proposition_2_3_iii A (A.con_sing x)
    | right y =>
      exact False.elim (not_mem_right_of_mem_left A B z hx0 hp)

end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
