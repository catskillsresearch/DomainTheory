/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.tensorR_app
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_bot

@[expose] public section


namespace DomainTheory.DataTypesAsLattices















/-- **Scott 1976, Theorem 4.4 (i), strictness.** -/
theorem tensorR_isStrict {a b : Pomega} (ha : IsStrict a) (hb : IsStrict b) :
    IsStrict (tensorR a b) := by
  change funOf (tensorR a b) botElem = botElem
  rw [tensorR_app, funOf_bot, funOf_bot, ha, hb, pairSeq_bot]

end DomainTheory.DataTypesAsLattices
