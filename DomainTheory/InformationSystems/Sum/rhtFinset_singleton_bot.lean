/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.Constructive
public import DomainTheory.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.Sum.SumToken
public import DomainTheory.InformationSystems.Sum.instDecidableEqSumToken
public import DomainTheory.InformationSystems.Sum.instLeftCommutativeLftInsert
public import DomainTheory.InformationSystems.Sum.instLeftCommutativeRhtInsert
public import DomainTheory.InformationSystems.Sum.rhtFinset
public import DomainTheory.InformationSystems.Sum.mem_rhtFinset

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

theorem rhtFinset_singleton_bot :
    rhtFinset ({.bot} : Finset (SumToken α β)) = ∅ := by
  ext y
  constructor
  · intro hy
    have : SumToken.right y ∈ ({.bot} : Finset _) := (mem_rhtFinset).1 hy
    exact False.elim (nomatch Finset.mem_singleton.mp this)
  · intro hy
    exact False.elim (Finset.notMem_empty y hy)

end InfoSys

end DomainTheory.InformationSystems
