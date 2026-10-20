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
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.liftSumRight
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.mem_liftSumRight

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β)

set_option linter.unusedSectionVars false

theorem lftFinset_liftSumRight (w : Finset β) :
    lftFinset (liftSumRight (α := α) w) = ∅ := by
  ext x
  constructor
  · intro hx
    rcases (mem_liftSumRight (α := α)).1 ((mem_lftFinset).1 hx) with ⟨_, _, h⟩
    exact False.elim (nomatch h)
  · intro hx
    exact False.elim (Finset.notMem_empty x hx)

end InfoSys

end DomainTheory.InformationSystems
