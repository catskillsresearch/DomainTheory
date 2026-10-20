/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Computability.Halting
import DomainTheory.DataTypesAsLattices.Computability
import DomainTheory.DataTypesAsLattices.Functionality
import DomainTheory.DataTypesAsLattices.Enumeration.Basic
import DomainTheory.DataTypesAsLattices.Enumeration.primrecPred_valEntryJustified


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code











theorem primrecPred_valTraceStruct : PrimrecPred valTraceStruct := by
  have h : PrimrecRel fun (tr : ValTrace) (e : ℕ × ℕ × ℕ) => valEntryJustified tr e :=
    primrecPred_valEntryJustified
  exact (PrimrecRel.forall_mem_list (R := fun e tr => valEntryJustified tr e)
      (h.comp Primrec.snd Primrec.fst)).comp Primrec.id Primrec.id

end DomainTheory.DataTypesAsLattices
