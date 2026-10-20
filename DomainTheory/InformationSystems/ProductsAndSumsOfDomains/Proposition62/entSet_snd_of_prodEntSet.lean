/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62.instLeftCommutativeMkLeftInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62.instLeftCommutativeMkRightInsert

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β)

/-- Product entailment of a set projects to component entailment on `snd`. -/
theorem entSet_snd_of_prodEntSet {u v : Finset (ProdToken A B)}
    (h : (productSystem A B).EntSet u v) :
    B.EntSet (sndFinset A B u) (sndFinset A B v) := by
  intro y hy
  rcases (mem_sndFinset A B).1 hy with ⟨p, hp, hbot, rfl⟩
  exact (h p hp).2.2 hbot

end InfoSys

end DomainTheory.InformationSystems
