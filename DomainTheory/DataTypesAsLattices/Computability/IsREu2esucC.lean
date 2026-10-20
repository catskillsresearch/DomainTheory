/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Computability.RE
import DomainTheory.DataTypesAsLattices.Lambda
import DomainTheory.DataTypesAsLattices.Computability.Basic
import DomainTheory.DataTypesAsLattices.Computability.REPredu2ecomp
import DomainTheory.DataTypesAsLattices.Computability.REPredu2eand
import DomainTheory.DataTypesAsLattices.Computability.primrec_testBit
import DomainTheory.DataTypesAsLattices.Computability.IsREu2esuccSet
import DomainTheory.DataTypesAsLattices.Computability.primrecPred_bool
import DomainTheory.DataTypesAsLattices.Computability.IsREu2egraph_of_primrecRel


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem IsRE.sucC : IsRE sucC := by
  have hp : PrimrecRel fun n m : ℕ => m ≠ 0 ∧ n.testBit m.pred = true :=
    (PrimrecPred.not (Primrec.eq.comp Primrec.snd (Primrec.const 0))).and
      (primrecPred_bool
        (Primrec₂.comp primrec_testBit Primrec.fst (Primrec.pred.comp Primrec.snd)))
  refine (IsRE.graph_of_primrecRel (f := DataTypesAsLattices.succSet)
      (hp.of_eq fun n m => ?_)).of_eq ?_
  · constructor
    · intro ⟨hm0, hbit⟩
      exact ⟨m.pred, mem_e.mpr hbit, (Nat.succ_pred_eq_of_ne_zero hm0).symm⟩
    · intro ⟨k, hk, hm⟩
      subst hm
      exact ⟨Nat.succ_ne_zero k, mem_e.mp hk⟩
  · intro p; rfl

end DomainTheory.DataTypesAsLattices
