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
import DomainTheory.DataTypesAsLattices.Computability.primrec_testBit
import DomainTheory.DataTypesAsLattices.Computability.REPredu2eor
import DomainTheory.DataTypesAsLattices.Computability.primrecPred_bool
import DomainTheory.DataTypesAsLattices.Computability.eSubset_e_iff


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem primrecRel_eSubset : PrimrecRel fun n b : ℕ => e n ⊆ e b := by
  have hR : PrimrecRel fun k q : ℕ =>
      q.unpair.1.testBit k = false ∨ q.unpair.2.testBit k = true :=
    ((primrecPred_bool
        (Primrec₂.comp primrec_testBit
          (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)) Primrec.fst)).not.or
      (primrecPred_bool
        (Primrec₂.comp primrec_testBit
          (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)) Primrec.fst))).of_eq
      fun _ => by simp [Bool.not_eq_true]
  refine (hR.forall_lt.comp Primrec.fst
      (Primrec₂.natPair.comp Primrec.fst Primrec.snd)).of_eq fun p => ?_
  simpa [Nat.unpair_pair] using (eSubset_e_iff p.1 p.2).symm

end DomainTheory.DataTypesAsLattices
