/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.InformationSystems.FunctionSpace
import DomainTheory.InformationSystems.Sum
import Mathlib.Data.Finset.Card
import DomainTheory.InformationSystems.Factoid82.Basic


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]





































variable (A : InfoSys α)





















/-- FunCon from an explicit right-branch witness at stage `n+1`. -/
theorem LamConN_fun_FunCon_right {n : ℕ} {u : Finset (RawLamToken α)}
    (_hA : lamAtomFinset u = ∅)
    (_hWF : ∀ p ∈ lamFunFinset u,
      LamConN A n (listToFinset p.1) ∧ LamConN A n (listToFinset p.2))
    (hFun : ∀ s ⊆ lamFunFinset u,
      LamConN A n (lamInputUnion s) → LamConN A n (lamOutputUnion s))
    {s : Finset (List (RawLamToken α) × List (RawLamToken α))}
    (hs : s ⊆ lamFunFinset u) (hIn : LamConN A n (lamInputUnion s)) :
    LamConN A n (lamOutputUnion s) :=
  hFun s hs hIn

end InfoSys
end DomainTheory.InformationSystems
