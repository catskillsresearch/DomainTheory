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
import DomainTheory.DataTypesAsLattices.Enumeration.valTraceHas_append_left
import DomainTheory.DataTypesAsLattices.Enumeration.valTraceHas_append_right
import DomainTheory.DataTypesAsLattices.Enumeration.valTraceOk_append
import DomainTheory.DataTypesAsLattices.Enumeration.valTraceOk_empty


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code









theorem exists_concat_traces {c : ℕ} (ks : List ℕ)
    (h : ∀ i ∈ ks, ∃ tr, valTraceOk tr ∧ valTraceHas tr c i) :
    ∃ tr, valTraceOk tr ∧ ∀ i ∈ ks, valTraceHas tr c i := by
  induction ks with
  | nil => exact ⟨[], valTraceOk_empty, fun _ hi => by simp at hi⟩
  | cons i is ih =>
      obtain ⟨tr₁, hok₁, hhas₁⟩ := h i (by simp)
      obtain ⟨tr₂, hok₂, hhas₂⟩ := ih fun j hj => h j (by simp [hj])
      refine ⟨tr₁ ++ tr₂, valTraceOk_append hok₁ hok₂, fun j hj => ?_⟩
      rcases List.mem_cons.mp hj with rfl | hj
      · exact valTraceHas_append_left hhas₁
      · exact valTraceHas_append_right (hhas₂ j hj)

end DomainTheory.DataTypesAsLattices
