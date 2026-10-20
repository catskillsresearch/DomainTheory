/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise414
import Mathlib.Tactic
import DomainTheory.Neighborhood.Exercise421.Basic


namespace DomainTheory.Neighborhood.Exercise421

open DomainTheory.Neighborhood.Exercise414









/-- The isomorphism sends `0` to the distinguished element `m` of `[m]`. -/
theorem addIso_zero (m : ℕ) : (addIso m 0 : ℕ) = m := by simp [addIso]

end DomainTheory.Neighborhood.Exercise421
