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
public import DomainTheory.InformationSystems.Factoid75.boolSystem
public import DomainTheory.InformationSystems.Factoid75.BasicInst22
public import DomainTheory.InformationSystems.Factoid75.strictFunctionSystem
public import DomainTheory.InformationSystems.Factoid75.approxMap_toStrictElement
public import DomainTheory.InformationSystems.Factoid75.condMap
public import DomainTheory.InformationSystems.Factoid75.IsStrict_condMap

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

open ApproximableMap

/-- `cond` as an element of `|BOOL →ₛ A|`. -/
def condElement (z : (productSystem A A).Element) :
    (strictFunctionSystem boolSystem A).Element :=
  approxMap_toStrictElement boolSystem A
    (condMap A ((fstMap A A).toElement z) ((sndMap A A).toElement z))
    (IsStrict_condMap A _ _)

end InfoSys

end DomainTheory.InformationSystems
