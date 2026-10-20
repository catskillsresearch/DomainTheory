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


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code









theorem valEntryJustified_mono {tr₁ tr₂ : ValTrace} {e : ℕ × ℕ × ℕ}
    (hsub : ∀ c m, valTraceHas tr₁ c m → valTraceHas tr₂ c m)
    (h : valEntryJustified tr₁ e) : valEntryJustified tr₂ e := by
  rcases h with h | ⟨hop, hbits⟩
  · exact Or.inl h
  · exact Or.inr ⟨hsub _ _ hop, fun i hi => (hbits i hi).imp_right (hsub _ _)⟩

end DomainTheory.DataTypesAsLattices
