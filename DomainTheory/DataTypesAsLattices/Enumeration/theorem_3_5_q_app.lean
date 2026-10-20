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
import DomainTheory.DataTypesAsLattices.Enumeration.valNat_fin


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices



































































/-- Appendix inclusion of Theorem 3.5: `val(p(fin j)) ⊆ q(e j)`. -/
theorem theorem_3_5_q_app (p : ℕ → ℕ) (j : ℕ) :
    valNat (p (fin j)) ⊆ funOf (myhillQ valNat p) (e j) := by
  intro m hm
  exact ⟨j, subset_rfl, ⟨j, m, rfl, by simpa [valNat_fin] using hm⟩⟩

end DomainTheory.DataTypesAsLattices
