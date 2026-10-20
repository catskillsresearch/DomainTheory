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
import DomainTheory.DataTypesAsLattices.Enumeration.REPredu2eexists_param
import DomainTheory.DataTypesAsLattices.Enumeration.valNat_mem_re
import DomainTheory.DataTypesAsLattices.Enumeration.realizes_valNat_mem
import DomainTheory.DataTypesAsLattices.Enumeration.funOf_ofNat_mem_re


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code













theorem valNat_mem_comp_primrec {u : Pomega} {p s : ℕ → ℕ} {k : ℕ}
    (hu : IsCombinatory u) (hr : Realizes u p) (hs : Primrec s) :
    REPred fun m => k ∈ valNat (p (s m)) := by
  have hinner : REPred fun q : ℕ × ℕ =>
      q.2 ∈ funOf u (ofNat (s q.1)) ∧ k ∈ valNat q.2 :=
    REPred.and
      ((funOf_ofNat_mem_re (combinatory_isRE hu)).comp
        (Primrec.pair (hs.comp Primrec.fst) Primrec.snd).to_comp)
      (valNat_mem_re.comp (Primrec.pair Primrec.snd (Primrec.const k)).to_comp)
  exact _root_.REPred.of_eq (REPred.exists_param (α := ℕ) hinner) fun m =>
    (realizes_valNat_mem hr (s m) k).symm

end DomainTheory.DataTypesAsLattices
