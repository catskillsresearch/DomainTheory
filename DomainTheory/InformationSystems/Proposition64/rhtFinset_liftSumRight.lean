/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.Sum
public import DomainTheory.InformationSystems.Factoid33
public import DomainTheory.InformationSystems.Proposition53
public import DomainTheory.InformationSystems.Proposition55
public import DomainTheory.InformationSystems.Proposition64.instLeftCommutativeLiftSumLeft
public import DomainTheory.InformationSystems.Proposition64.instLeftCommutativeLiftSumRight
public import DomainTheory.InformationSystems.Proposition64.liftSumRight
public import DomainTheory.InformationSystems.Proposition64.mem_liftSumRight

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β)

set_option linter.unusedSectionVars false

theorem rhtFinset_liftSumRight (w : Finset β) :
    rhtFinset (liftSumRight (α := α) w) = w := by
  ext y
  simp only [mem_rhtFinset, mem_liftSumRight]
  exact ⟨fun ⟨z, hz, h⟩ => by injection h with h'; exact h' ▸ hz,
    fun hy => ⟨y, hy, rfl⟩⟩

end InfoSys

end DomainTheory.InformationSystems
