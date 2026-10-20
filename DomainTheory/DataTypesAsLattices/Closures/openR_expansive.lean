/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Algebra.Ring.Parity
import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Closures.Basic
import DomainTheory.DataTypesAsLattices.Closures.openR_app


namespace DomainTheory.DataTypesAsLattices



































theorem openR_expansive (u : Pomega) : u ⊆ funOf openR u := by
  intro k hk
  rw [openR_app]
  exact ⟨k, subset_rfl, hk⟩

end DomainTheory.DataTypesAsLattices
