/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Algebra.Ring.Parity
import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Closures.Basic
import DomainTheory.DataTypesAsLattices.Closures.zero_mem_boxShift_app


namespace DomainTheory.DataTypesAsLattices































theorem boxShift_app_ne_bot (a x : Pomega) : funOf (boxShift a) x ≠ botElem := by
  intro h
  have h0 := zero_mem_boxShift_app a x
  rw [h] at h0
  simp [botElem] at h0

end DomainTheory.DataTypesAsLattices
