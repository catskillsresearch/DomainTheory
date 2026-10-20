/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_zero
import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_one
import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_inj
import DomainTheory.DataTypesAsLattices.Functionality.tensorR_app


namespace DomainTheory.DataTypesAsLattices















theorem typed_pairSeq_tensorR (a b x y : Pomega) :
    typed (pairSeq x y) (tensorR a b) ↔ typed x a ∧ typed y b := by
  constructor
  · intro h
    have h' : pairSeq x y =
        pairSeq (funOf a x) (funOf b y) := by
      rw [typed, tensorR_app, pairSeq_app_zero, pairSeq_app_one] at h
      exact h
    exact pairSeq_inj h'
  · intro ⟨hx, hy⟩
    rw [typed, tensorR_app, pairSeq_app_zero, pairSeq_app_one, ← hx, ← hy]

end DomainTheory.DataTypesAsLattices
