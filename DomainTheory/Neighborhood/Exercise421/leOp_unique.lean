/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise414
import Mathlib.Tactic
import DomainTheory.Neighborhood.Exercise421.Basic
import DomainTheory.Neighborhood.Exercise421.mem_fixedPoint_iff


namespace DomainTheory.Neighborhood.Exercise421

open DomainTheory.Neighborhood.Exercise414




/-- **Exercise 4.21 (Scott 1981, PRG-19).** The order relation `≤` is the **unique** fixed point of
Scott's equation: any `u` with `leOp u = u` equals `leRel`. -/
theorem leOp_unique {u : Set (ℕ × ℕ)} (hu : leOp u = u) : u = leRel := by
  ext ⟨n, m⟩
  rw [mem_fixedPoint_iff hu]
  rfl

end DomainTheory.Neighborhood.Exercise421
