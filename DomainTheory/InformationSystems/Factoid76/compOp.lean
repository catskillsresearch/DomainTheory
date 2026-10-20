/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.Theorem72
public import DomainTheory.InformationSystems.Proposition56
public import DomainTheory.InformationSystems.Factoid76.compOpUncurry

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

open ApproximableMap

set_option linter.unusedSectionVars false

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

/-- **Factoid 7.6.** Operator `comp : (B → C) × (A → B) → (A → C)`. -/
def compOp : ApproximableMap
    (productSystem (functionSystem B C) (functionSystem A B))
    (functionSystem A C) :=
  curryMap (productSystem (functionSystem B C) (functionSystem A B)) A C
    (compOpUncurry A B C)

end InfoSys

end DomainTheory.InformationSystems
