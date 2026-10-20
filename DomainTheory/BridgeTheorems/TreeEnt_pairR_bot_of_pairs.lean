/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81
public import DomainTheory.BridgeTheorems.SexDomainEquationInst10
public import DomainTheory.BridgeTheorems.SexDomainEquationInst15

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem TreeEnt_pairR_bot_of_pairs {u : Finset (TreeToken α)}
    (hu : TreeCon A u) (h : pairLFinset u ≠ ∅ ∨ pairRFinset u ≠ ∅) :
    TreeEnt A u (.pairR .bot) :=
  ⟨hu, TreeCon_atoms_empty_of_right A hu h,
    TreeCon_pairR_of_right A hu (TreeCon_atoms_empty_of_right A hu h),
    TreeCon_pairL_of_right A hu (TreeCon_atoms_empty_of_right A hu h),
    h.elim (fun hL => Or.inr ⟨rfl, hL⟩) (fun hR => Or.inl ⟨hR, trivial⟩)⟩

end DomainTheory.BridgeTheorems
