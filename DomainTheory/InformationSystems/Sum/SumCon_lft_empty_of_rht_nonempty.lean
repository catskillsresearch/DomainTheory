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
public import DomainTheory.InformationSystems.Sum.lftFinset
public import DomainTheory.InformationSystems.Sum.rhtFinset
public import DomainTheory.InformationSystems.Sum.SumCon

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

theorem SumCon_lft_empty_of_rht_nonempty {u : Finset (SumToken α β)}
    (hu : SumCon A B u) (hne : rhtFinset u ≠ ∅) : lftFinset u = ∅ := by
  rcases hu with ⟨_, hr⟩ | ⟨hl, _⟩
  · exact False.elim (hne hr)
  · exact hl

end InfoSys

end DomainTheory.InformationSystems
