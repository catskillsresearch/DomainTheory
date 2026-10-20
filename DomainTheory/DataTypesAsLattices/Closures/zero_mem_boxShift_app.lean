/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Algebra.Ring.Parity
import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Closures.Basic
import DomainTheory.DataTypesAsLattices.Closures.boxShift_app


namespace DomainTheory.DataTypesAsLattices































theorem zero_mem_boxShift_app (a x : Pomega) : (0 : ℕ) ∈ funOf (boxShift a) x := by
  rw [boxShift_app]
  exact Or.inl (by simp [ofNat])

end DomainTheory.DataTypesAsLattices
