/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Computability.RE
import DomainTheory.DataTypesAsLattices.Lambda
import DomainTheory.DataTypesAsLattices.Computability.Basic
import DomainTheory.DataTypesAsLattices.Computability.REPredu2eexists
import DomainTheory.DataTypesAsLattices.Computability.primrecPred_common_stage
import DomainTheory.DataTypesAsLattices.Computability.eSubset_iff_stage


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

/-- Finite inclusion `e n ⊆ x` is r.e. in `n` when `x` is, via one common `evaln` stage. -/
theorem IsRE.eSubset {x : Pomega} (hx : IsRE x) :
    REPred fun n => e n ⊆ x := by
  have hf : Partrec fun k : ℕ =>
      (Part.assert (k ∈ x) fun _ => Part.some (0 : ℕ)) :=
    hx.map (Computable.const (0 : ℕ)).to₂
  obtain ⟨c, hc⟩ := Code.exists_code.1 (Partrec.nat_iff.1 hf)
  have hex : REPred fun n =>
      ∃ s, ∀ k < n, n.testBit k = false ∨ (evaln s c k).isSome = true :=
    REPred.exists (p := fun n s =>
        ∀ k < n, n.testBit k = false ∨ (evaln s c k).isSome = true)
      (primrecPred_common_stage c).computablePred.to_re
  exact hex.of_eq fun n => (eSubset_iff_stage hc n).symm

end DomainTheory.DataTypesAsLattices
