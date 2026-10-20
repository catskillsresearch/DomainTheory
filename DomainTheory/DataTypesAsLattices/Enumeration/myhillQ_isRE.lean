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
import DomainTheory.DataTypesAsLattices.Enumeration.primrec_fin
import DomainTheory.DataTypesAsLattices.Enumeration.primrec_unpairComp
import DomainTheory.DataTypesAsLattices.Enumeration.REPredu2eexists_param
import DomainTheory.DataTypesAsLattices.Enumeration.valNat_mem_re
import DomainTheory.DataTypesAsLattices.Enumeration.mem_myhillQ
import DomainTheory.DataTypesAsLattices.Enumeration.realizes_valNat_mem
import DomainTheory.DataTypesAsLattices.Enumeration.funOf_ofNat_mem_re


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code











theorem myhillQ_isRE {u : Pomega} {p : ℕ → ℕ}
    (hu : IsCombinatory u) (hr : Realizes u p) :
    IsRE (myhillQ valNat p) := by
  have hmem : REPred fun q : ℕ × ℕ =>
      q.2 ∈ valNat (p (fin q.1)) := by
    have hinner : REPred fun q : (ℕ × ℕ) × ℕ =>
        q.2 ∈ funOf u (ofNat (fin q.1.1)) ∧ q.1.2 ∈ valNat q.2 :=
      REPred.and
        ((funOf_ofNat_mem_re (combinatory_isRE hu)).comp
          (Primrec.pair (primrec_fin.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd).to_comp)
        (valNat_mem_re.comp (Primrec.pair Primrec.snd (Primrec.snd.comp Primrec.fst)).to_comp)
    exact _root_.REPred.of_eq (REPred.exists_param (α := ℕ × ℕ) hinner) fun q =>
      (realizes_valNat_mem hr (fin q.1) q.2).symm
  exact _root_.REPred.of_eq
    (hmem.comp (primrec_unpairComp.to_comp))
    fun k => (mem_myhillQ p k).symm

end DomainTheory.DataTypesAsLattices
