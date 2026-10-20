/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Data.Multiset.MapFold
import DomainTheory.InformationSystems.FunctionSpace
import DomainTheory.InformationSystems.Theorem72
import DomainTheory.InformationSystems.Factoid25
import DomainTheory.InformationSystems.Factoid33
import DomainTheory.InformationSystems.Factoid35
import DomainTheory.InformationSystems.Factoid75.Basic
import DomainTheory.InformationSystems.Factoid75.condMap_toElement_boolTrue
import DomainTheory.InformationSystems.Factoid75.condMap_toElement_boolFalse


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
