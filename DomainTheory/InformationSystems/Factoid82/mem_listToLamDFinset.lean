/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.FunctionSpace
public import DomainTheory.InformationSystems.Sum
public import Mathlib.Data.Finset.Card
import all Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.Factoid82.LamEntDepth
public import DomainTheory.InformationSystems.Factoid82.LamEntDepth
public import DomainTheory.InformationSystems.Factoid82.BasicInst23
public import DomainTheory.InformationSystems.Factoid82.BasicInst27
public import DomainTheory.InformationSystems.Factoid82.IsLamWF
public import DomainTheory.InformationSystems.Factoid82.LamDToken
public import DomainTheory.InformationSystems.Factoid82.BasicInst70
public import DomainTheory.InformationSystems.Factoid82.BasicInst74
public import DomainTheory.InformationSystems.Factoid82.listToLamDFinset

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

theorem mem_listToLamDFinset {xs : List (RawLamToken α)}
    {h : ∀ t ∈ xs, IsLamWF A t} {p : LamDToken A} :
    p ∈ listToLamDFinset A xs h ↔ p.val ∈ xs := by
  induction xs with
  | nil =>
    constructor
    · intro hp; exact False.elim (Finset.notMem_empty _ hp)
    · intro hp; cases hp
  | cons t ts ih =>
    constructor
    · intro hp
      rcases Finset.mem_insert.mp hp with hp | hp
      · subst hp; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih.1 hp)
    · intro hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (ih.2 hp)

end InfoSys

end DomainTheory.InformationSystems
