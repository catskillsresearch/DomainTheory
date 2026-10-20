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
import DomainTheory.DataTypesAsLattices.Enumeration.valNat_mem_iff
import DomainTheory.DataTypesAsLattices.Enumeration.primrecRel_valTraceHas
import DomainTheory.DataTypesAsLattices.Enumeration.REPredu2eexists_param
import DomainTheory.DataTypesAsLattices.Enumeration.valTraceOk_re


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code











/-- Uniform r.e. membership in `val`. -/
theorem valNat_mem_re : REPred fun q : ℕ × ℕ => q.2 ∈ valNat q.1 := by
  have htr : REPred fun q : (ℕ × ℕ) × ValTrace =>
      valTraceOk q.2 ∧ valTraceHas q.2 q.1.1 q.1.2 :=
    REPred.and (valTraceOk_re.comp Computable.snd)
      ((primrecRel_valTraceHas.comp Primrec.snd Primrec.fst).computablePred.to_re)
  have hN : REPred fun q : (ℕ × ℕ) × ℕ =>
      valTraceOk ((decode q.2 : Option ValTrace).getD []) ∧
        valTraceHas ((decode q.2).getD []) q.1.1 q.1.2 :=
    htr.comp (Computable.pair Computable.fst
      (Computable.option_getD (Computable.decode.comp Computable.snd)
        (Computable.const [])))
  have hex : REPred fun q : ℕ × ℕ =>
      ∃ tr, valTraceOk tr ∧ valTraceHas tr q.1 q.2 :=
    _root_.REPred.of_eq
      (REPred.exists_param (α := ℕ × ℕ)
        (p := fun q enc =>
          valTraceOk ((decode enc : Option ValTrace).getD []) ∧
            valTraceHas ((decode enc).getD []) q.1 q.2)
        hN)
      fun q =>
      ⟨fun ⟨enc, henc⟩ => ⟨(decode enc).getD [], henc⟩, fun ⟨tr, hok⟩ =>
        ⟨encode tr, by simpa [encodek] using hok⟩⟩
  exact _root_.REPred.of_eq hex fun q => (valNat_mem_iff q.1 q.2).symm

end DomainTheory.DataTypesAsLattices
