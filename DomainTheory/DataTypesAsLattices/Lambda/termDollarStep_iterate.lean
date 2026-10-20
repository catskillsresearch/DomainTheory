/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic
import DomainTheory.DataTypesAsLattices.Lambda.funOf_bot
import DomainTheory.DataTypesAsLattices.Lambda.seqFunLt_zero
import DomainTheory.DataTypesAsLattices.Lambda.seqFunLt_succ_term
import DomainTheory.DataTypesAsLattices.Lambda.termDollarStep_app2


namespace DomainTheory.DataTypesAsLattices






















































theorem termDollarStep_iterate (n : ℕ) (u z : Pomega) :
    funOf (funOf (iterateBot termDollarStep n) u) z = seqFunLt u z n := by
  induction n generalizing u z with
  | zero =>
    simp [iterateBot, funOf_bot, seqFunLt_zero]
  | succ n ih =>
    rw [iterateBot, termDollarStep_app2, termDollarStepBody, ih, seqFunLt_succ_term]

end DomainTheory.DataTypesAsLattices
