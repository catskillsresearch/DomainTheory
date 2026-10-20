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
public import DomainTheory.InformationSystems.Factoid82.LamConDepth_insert_of_ent
public import DomainTheory.InformationSystems.Factoid82.LamDToken
public import DomainTheory.InformationSystems.Factoid82.BasicInst70
public import DomainTheory.InformationSystems.Factoid82.BasicInst74
public import DomainTheory.InformationSystems.Factoid82.lamDForgetFinset_insert
public import DomainTheory.InformationSystems.Factoid82.LamDCon
public import DomainTheory.InformationSystems.Factoid82.LamDEnt

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

theorem LamDCon_insert_of_ent {u : Finset (LamDToken A)} {p : LamDToken A}
    (ht : LamDEnt A u p) : LamDCon A (insert p u) := by
  rw [LamDCon, lamDForgetFinset_insert]
  exact LamConDepth_insert_of_ent A ht

end InfoSys

end DomainTheory.InformationSystems
