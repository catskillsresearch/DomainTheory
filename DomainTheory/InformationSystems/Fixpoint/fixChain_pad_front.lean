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

theorem fixChain_pad_front {w : Finset (FunToken A A)} {n : Nat} {v : Finset α}
    (hw : FunCon A A w) (h : FixChain A w n v) : FixChain A w (n + 1) v := by
  induction n generalizing v with
  | zero =>
    rw [h]
    refine ⟨∅, rfl, A.con_empty, A.con_empty, ?_⟩
    exact (functionSystem A A).ent_bot hw
  | succ n ih =>
    obtain ⟨u, hu, huC, hvC, hEnt⟩ := h
    exact ⟨u, ih hu, huC, hvC, hEnt⟩

end InfoSys

end DomainTheory.InformationSystems
