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
import DomainTheory.DataTypesAsLattices.Computability.primrecRel_mem_funOf_e


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem primrecRel_eSubset_funOf_e_bit :
    PrimrecRel fun i kq : ℕ =>
      (Nat.unpair kq).1.testBit i = false ∨
        i ∈ e (Nat.unpair (Nat.unpair kq).2).1 ⬝
          e (Nat.unpair (Nat.unpair kq).2).2 :=
  ((primrecPred_bool (Primrec₂.comp primrec_testBit
      (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))
      Primrec.fst)).not.or
    (primrecRel_mem_funOf_e.comp
      (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))
      Primrec.fst)).of_eq fun p => by
    simp [Bool.not_eq_true]

end DomainTheory.DataTypesAsLattices
