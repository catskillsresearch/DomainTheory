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
import DomainTheory.DataTypesAsLattices.Enumeration.Deg_isSubalgebra
import DomainTheory.DataTypesAsLattices.Enumeration.Deg_self
import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSubalgebra_isSubalgebra
import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSubalgebra_generator
import DomainTheory.DataTypesAsLattices.Enumeration.combinatory_mem_subalgebra
import DomainTheory.DataTypesAsLattices.Enumeration.theorem_3_6_generated


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code






















































/-- Exact finite-generation classification of enumeration degrees. -/
theorem theorem_3_6 (A : Set Pomega) :
    (∃ a, A = Deg a) ↔
      ∃ xs : List Pomega, A = GeneratedSubalgebra xs := by
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨[a], ?_⟩
    ext u
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact (GeneratedSubalgebra_isSubalgebra [a]).2
        (combinatory_mem_subalgebra (GeneratedSubalgebra_isSubalgebra [a]) hr)
        (GeneratedSubalgebra_generator (by simp))
    · intro hu
      exact hu _ (Deg_isSubalgebra a) (by
        intro x hx
        simp at hx
        subst x
        exact Deg_self a)
  · rintro ⟨xs, rfl⟩
    exact ⟨singleGenerator xs, theorem_3_6_generated xs⟩

end DomainTheory.DataTypesAsLattices
