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
import DomainTheory.DataTypesAsLattices.Computability.primrec_pack4_proj2
import DomainTheory.DataTypesAsLattices.Computability.primrec_pack4_proj3


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code



theorem primrecRel_Scomb_bit :
    PrimrecRel fun i kt : ℕ =>
      (Nat.unpair kt).1.testBit i = false ∨
        i ∈ e (pack4_proj2 (Nat.unpair kt).2) ⬝
          e (pack4_proj3 (Nat.unpair kt).2) :=
  ((primrecPred_bool (Primrec₂.comp primrec_testBit
      (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))
      Primrec.fst)).not.or
    (primrecRel_mem_funOf_e.comp
      (Primrec₂.natPair.comp
        (primrec_pack4_proj2.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))
        (primrec_pack4_proj3.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))))
      Primrec.fst)).of_eq fun p => by simp [Bool.not_eq_true]

end DomainTheory.DataTypesAsLattices
