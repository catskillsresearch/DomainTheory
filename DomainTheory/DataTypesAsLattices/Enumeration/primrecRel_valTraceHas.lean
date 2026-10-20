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
import DomainTheory.DataTypesAsLattices.Enumeration.valTraceHas_iff


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code











theorem primrecRel_valTraceHas :
    PrimrecRel fun (tr : ValTrace) (p : ℕ × ℕ) => valTraceHas tr p.1 p.2 := by
  have h : PrimrecRel fun (tr : ValTrace) (p : ℕ × ℕ) =>
      ∃ e ∈ tr, e.1 = p.1 ∧ e.2.1 = p.2 :=
    PrimrecRel.exists_mem_list
      ((Primrec.eq.comp (Primrec.fst.comp Primrec.fst)
          (Primrec.fst.comp Primrec.snd)).and
        (Primrec.eq.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.snd.comp Primrec.snd)))
  exact h.of_eq fun tr p => (valTraceHas_iff tr p.1 p.2).symm

end DomainTheory.DataTypesAsLattices
