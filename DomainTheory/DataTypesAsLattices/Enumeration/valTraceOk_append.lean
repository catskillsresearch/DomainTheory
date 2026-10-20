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
import DomainTheory.DataTypesAsLattices.Enumeration.valEntryJustified_mono


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code









theorem valTraceOk_append {tr₁ tr₂ : ValTrace}
    (h₁ : valTraceOk tr₁) (h₂ : valTraceOk tr₂) :
    valTraceOk (tr₁ ++ tr₂) := by
  constructor
  · intro e he
    rcases List.mem_append.mp he with he | he
    · exact valEntryJustified_mono (fun _ _ => valTraceHas_append_left) (h₁.1 e he)
    · exact valEntryJustified_mono (fun _ _ => valTraceHas_append_right) (h₂.1 e he)
  · intro e he he0
    rcases List.mem_append.mp he with he | he
    · exact h₁.2 e he he0
    · exact h₂.2 e he he0

end DomainTheory.DataTypesAsLattices
