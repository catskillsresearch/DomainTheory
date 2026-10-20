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
public import DomainTheory.InformationSystems.Factoid82.LamDToken
public import DomainTheory.InformationSystems.Factoid82.BasicInst70
public import DomainTheory.InformationSystems.Factoid82.lamDBot
public import DomainTheory.InformationSystems.Factoid82.BasicInst74
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

theorem LamDEnt_bot {u : Finset (LamDToken A)} (hu : LamDCon A u) :
    LamDEnt A u (lamDBot A) :=
  LamEntDepth.bot hu

end InfoSys

end DomainTheory.InformationSystems
