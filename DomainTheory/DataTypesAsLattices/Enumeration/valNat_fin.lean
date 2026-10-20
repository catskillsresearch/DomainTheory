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
import DomainTheory.DataTypesAsLattices.Enumeration.valNat_finAux


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

































































/-- **Scott 1976, before Theorem 3.5.** `val(fin j) = e j`. -/
theorem valNat_fin (j : ℕ) : valNat (fin j) = e j :=
  by
    rw [fin, valNat_finAux]
    ext n
    simp only [Set.mem_ofPred_eq, mem_e]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨Nat.lt_succ_of_le (mem_e_le (mem_e.mpr h)), h⟩

end DomainTheory.DataTypesAsLattices
