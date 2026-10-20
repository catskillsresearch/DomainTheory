/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise414
import Mathlib.Tactic
import DomainTheory.Neighborhood.Exercise421.Basic
import DomainTheory.Neighborhood.Exercise421.addIso_apply


namespace DomainTheory.Neighborhood.Exercise421

open DomainTheory.Neighborhood.Exercise414









/-- The isomorphism preserves the successor: `addIso m (n⁺) = (addIso m n)⁺`. -/
theorem addIso_succ (m n : ℕ) : (addIso m (n + 1) : ℕ) = (addIso m n : ℕ) + 1 := by
  simp only [addIso_apply]; omega

end DomainTheory.Neighborhood.Exercise421
