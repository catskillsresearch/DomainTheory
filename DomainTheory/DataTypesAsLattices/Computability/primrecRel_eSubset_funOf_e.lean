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
import DomainTheory.DataTypesAsLattices.Computability.eSubset_funOf_e_iff
import DomainTheory.DataTypesAsLattices.Computability.primrecRel_eSubset_funOf_e_bit


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem primrecRel_eSubset_funOf_e :
    PrimrecRel fun k q : ℕ =>
      e k ⊆ e (Nat.unpair q).1 ⬝ e (Nat.unpair q).2 := by
  refine (primrecRel_eSubset_funOf_e_bit.forall_lt.comp Primrec.fst
      (Primrec₂.natPair.comp Primrec.fst Primrec.snd)).of_eq fun p => ?_
  simp only [Nat.unpair_pair]
  exact (eSubset_funOf_e_iff p.1 p.2.unpair.1 p.2.unpair.2).symm

end DomainTheory.DataTypesAsLattices
