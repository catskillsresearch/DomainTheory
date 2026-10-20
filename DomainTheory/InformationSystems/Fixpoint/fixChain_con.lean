/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.Theorem72
public import DomainTheory.InformationSystems.Factoid33
public import DomainTheory.InformationSystems.Fixpoint.FixChain

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem fixChain_con {w : Finset (FunToken A A)} {n : Nat} {v : Finset α}
    (h : FixChain A w n v) : v ∈ A.Con := by
  match n with
  | 0 =>
    rw [h]
    exact A.con_empty
  | n + 1 =>
    obtain ⟨_, _, _, hv, _⟩ := h
    exact hv

end InfoSys

end DomainTheory.InformationSystems
