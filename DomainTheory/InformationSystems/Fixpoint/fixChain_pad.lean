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
public import DomainTheory.InformationSystems.Fixpoint.fixChain_pad_front

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem fixChain_pad {w : Finset (FunToken A A)} {n k : Nat} {v : Finset α}
    (hw : FunCon A A w) (h : FixChain A w n v) : FixChain A w (n + k) v := by
  induction k with
  | zero => exact h
  | succ k ih => exact fixChain_pad_front A hw ih

end InfoSys

end DomainTheory.InformationSystems
