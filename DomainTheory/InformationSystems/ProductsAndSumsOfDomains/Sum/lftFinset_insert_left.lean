/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.SumToken
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.instDecidableEqSumToken
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.instLeftCommutativeLftInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.instLeftCommutativeRhtInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.lftFinset
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.mem_lftFinset

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

theorem lftFinset_insert_left (u : Finset (SumToken α β)) (x : α) :
    lftFinset (insert (.left x) u) = insert x (lftFinset u) := by
  ext y
  constructor
  · intro hy
    have : SumToken.left y ∈ insert (.left x) u := (mem_lftFinset).1 hy
    rcases Finset.mem_insert.mp this with h | h
    · injection h with hy'
      exact Finset.mem_insert.mpr (Or.inl hy')
    · exact Finset.mem_insert.mpr (Or.inr ((mem_lftFinset).2 h))
  · intro hy
    rcases Finset.mem_insert.mp hy with hy' | hy'
    · exact (mem_lftFinset).2 (Finset.mem_insert.mpr (Or.inl (congrArg SumToken.left hy')))
    · exact (mem_lftFinset).2 (Finset.mem_insert.mpr (Or.inr ((mem_lftFinset).1 hy')))

end InfoSys

end DomainTheory.InformationSystems
