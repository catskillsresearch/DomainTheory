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
import DomainTheory.DataTypesAsLattices.Functionality.tensorR_app


namespace DomainTheory.DataTypesAsLattices















/-- **Scott 1976, Theorem 4.4 (ii).** `u : a ⊗ b` iff `u = ⟨u₀, u₁⟩`
with `u₀ : a` and `u₁ : b`. -/
theorem theorem_4_4_typed {a b u : Pomega} :
    typed u (tensorR a b) ↔
      u = pairSeq (funOf u (ofNat 0)) (funOf u (ofNat 1)) ∧
        typed (funOf u (ofNat 0)) a ∧ typed (funOf u (ofNat 1)) b := by
  constructor
  · intro hu
    have hpair : u =
        pairSeq (funOf a (funOf u (ofNat 0)))
          (funOf b (funOf u (ofNat 1))) := by
      simpa [typed, tensorR_app] using hu
    have h0 : funOf u (ofNat 0) = funOf a (funOf u (ofNat 0)) := by
      have := congrArg (fun w => funOf w (ofNat 0)) hpair
      simpa [pairSeq_app_zero] using this
    have h1 : funOf u (ofNat 1) = funOf b (funOf u (ofNat 1)) := by
      have := congrArg (fun w => funOf w (ofNat 1)) hpair
      simpa [pairSeq_app_one] using this
    refine ⟨hpair.trans (congr (congrArg pairSeq h0.symm) h1.symm), h0, h1⟩
  · intro ⟨hpair, ha, hb⟩
    change u = funOf (tensorR a b) u
    rw [tensorR_app, ← ha, ← hb, ← hpair]

end DomainTheory.DataTypesAsLattices
