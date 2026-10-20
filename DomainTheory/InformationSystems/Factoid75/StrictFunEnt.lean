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
public import DomainTheory.InformationSystems.Factoid75.StrictFunToken
public import DomainTheory.InformationSystems.Factoid75.BasicInst22
public import DomainTheory.InformationSystems.Factoid75.toFunFinset
public import DomainTheory.InformationSystems.Factoid75.StrictFunCon

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

/-- Entailment for `A →ₛ B`. -/
def StrictFunEnt (w : Finset (StrictFunToken A B)) (p : StrictFunToken A B) : Prop :=
  StrictFunCon A B w ∧ FunEnt A B (toFunFinset A B w) p.val

end InfoSys

end DomainTheory.InformationSystems
