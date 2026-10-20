/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import Mathlib.Data.Multiset.MapFold
import all Mathlib.Data.Multiset.MapFold
public import DomainTheory.InformationSystems.FunctionSpace
public import DomainTheory.InformationSystems.Theorem72
public import DomainTheory.InformationSystems.Factoid25
public import DomainTheory.InformationSystems.Factoid33
public import DomainTheory.InformationSystems.Factoid35
public import DomainTheory.InformationSystems.Factoid75.BoolToken
public import DomainTheory.InformationSystems.Factoid75.BoolPoint
public import DomainTheory.InformationSystems.Factoid75.boolSat
public import DomainTheory.InformationSystems.Factoid75.boolSat_bot
public import DomainTheory.InformationSystems.Factoid75.boolSat_sing

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

/-- **Factoid 7.5.** Flat BOOL information system. -/
def boolSystem : InfoSys BoolToken :=
  Factoid25.ofSatisfaction boolSat .bot boolSat_bot boolSat_sing

end InfoSys

end DomainTheory.InformationSystems
