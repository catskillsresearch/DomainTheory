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

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β)

set_option linter.unusedSectionVars false



















namespace ApproximableMap

variable {C : InfoSys γ}









/-- Choice-free emptiness dichotomy for `rhtFinset`. -/
theorem rhtFinset_eq_empty_or_mem (u : Finset (SumToken α β)) :
    rhtFinset u = ∅ ∨ ∃ y, y ∈ rhtFinset u := by
  induction u using Finset.induction_on with
  | empty =>
    exact Or.inl rhtFinset_empty
  | insert p s _hp ih =>
    cases p with
    | right y =>
      exact Or.inr ⟨y, by rw [rhtFinset_insert_right]; exact Finset.mem_insert_self _ _⟩
    | left x =>
      rw [rhtFinset_insert_left]; exact ih
    | bot =>
      rw [rhtFinset_insert_bot]; exact ih

end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
