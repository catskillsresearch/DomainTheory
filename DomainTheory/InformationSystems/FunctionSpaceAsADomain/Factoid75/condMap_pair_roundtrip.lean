/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import Mathlib.Data.Multiset.MapFold
import all Mathlib.Data.Multiset.MapFold
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.InformationSystems.Factoid25
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.Basic
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.condMap_toElement_boolTrue
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.condMap_toElement_boolFalse

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α β : Type*} [DecidableEq α] [DecidableEq β]







variable (A : InfoSys α) (B : InfoSys β)


























open ApproximableMap













/-- One direction of the conditional isomorphism on pairs. -/
theorem condMap_pair_roundtrip (x y : A.Element) :
    (condMap A x y).toElement boolTrue = x ∧
    (condMap A x y).toElement boolFalse = y :=
  ⟨condMap_toElement_boolTrue A x y, condMap_toElement_boolFalse A x y⟩

end InfoSys
end DomainTheory.InformationSystems
