/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.Theorem72
public import DomainTheory.InformationSystems.Proposition56
public import DomainTheory.InformationSystems.Factoid76.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

open ApproximableMap

set_option linter.unusedSectionVars false

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)







theorem pairOp_uncurry :
    uncurryMap (productSystem (functionSystem C A) (functionSystem C B)) C (productSystem A B)
      (pairOp A B C) =
      pairOpUncurry A B C := by
  simp only [pairOp, uncurry_curryMap]

end InfoSys
end DomainTheory.InformationSystems
