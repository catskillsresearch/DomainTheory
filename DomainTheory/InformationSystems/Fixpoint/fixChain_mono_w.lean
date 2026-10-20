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

theorem fixChain_mono_w {w w' : Finset (FunToken A A)} {n : Nat} {v : Finset α}
    (hw : FunCon A A w) (hw' : FunCon A A w') (h : FixChain A w n v)
    (hEntw : (functionSystem A A).EntSet w' w) : FixChain A w' n v := by
  induction n generalizing v with
  | zero => exact h
  | succ n ih =>
    obtain ⟨u, hu, huC, hvC, hEnt⟩ := h
    refine ⟨u, ih hu, huC, hvC, ?_⟩
    exact (functionSystem A A).ent_trans hw' hw hEntw hEnt

end InfoSys

end DomainTheory.InformationSystems
