/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.FixedLattices
import DomainTheory.DataTypesAsLattices.Lambda
import DomainTheory.DataTypesAsLattices.Retracts.Basic
import DomainTheory.DataTypesAsLattices.Retracts.arrowR_app


namespace DomainTheory.DataTypesAsLattices









































theorem arrowR_isStrict {a b : Pomega} (hb : IsStrict b) :
    IsStrict (arrowR a b) := by
  change funOf (arrowR a b) botElem = botElem
  rw [arrowR_app]
  have hbot : comp botElem a = botElem := by
    unfold comp
    simp [funOf_botElem, graph_const_bot]
  rw [hbot]
  unfold comp
  simp only [funOf_botElem]
  exact (congrArg graph (funext fun _ => hb)).trans graph_const_bot

end DomainTheory.DataTypesAsLattices
