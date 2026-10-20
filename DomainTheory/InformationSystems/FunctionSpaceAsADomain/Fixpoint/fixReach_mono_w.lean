/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.FixReach
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.fixChain_mono_w

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem fixReach_mono_w {w w' : Finset (FunToken A A)} {v : Finset α}
    (hw : FunCon A A w) (hw' : FunCon A A w') (h : FixReach A w v)
    (hEntw : (functionSystem A A).EntSet w' w) : FixReach A w' v := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, fixChain_mono_w A hw hw' hn hEntw⟩

end InfoSys

end DomainTheory.InformationSystems
