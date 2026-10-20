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
import DomainTheory.DataTypesAsLattices.Enumeration.valEntryJustified_mono


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code









theorem valTraceOk_cons {tr : ValTrace} {e : ℕ × ℕ × ℕ}
    (htr : valTraceOk tr) (hjust : valEntryJustified (e :: tr) e)
    (hg : e.1 = 0 → e.2.1 ∈ Gcomb) :
    valTraceOk (e :: tr) := by
  constructor
  · intro e' he'
    rcases List.mem_cons.mp he' with rfl | he'
    · exact hjust
    · exact valEntryJustified_mono
        (fun c m ⟨t, ht⟩ => ⟨t, List.mem_cons.mpr (Or.inr ht)⟩) (htr.1 e' he')
  · intro e' he' he0
    rcases List.mem_cons.mp he' with rfl | he'
    · exact hg he0
    · exact htr.2 e' he' he0

end DomainTheory.DataTypesAsLattices
