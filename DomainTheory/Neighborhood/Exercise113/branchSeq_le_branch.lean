/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.ExampleB
import DomainTheory.Neighborhood.Theorem111
import Mathlib.Tactic
import DomainTheory.Neighborhood.Exercise113.Basic


namespace DomainTheory.Neighborhood.Exercise113

open DomainTheory.Neighborhood NeighborhoodSystem ExampleB








/-- Every finite approximation `(p ↾ n)⊥` approximates the limit element `branch p`. -/
theorem branchSeq_le_branch (p : ℕ → Bool) (n : ℕ) : branchSeq p n ≤ branch p :=
  B.le_iUnion (branchSeq p) (branchSeq_mono p) n

end DomainTheory.Neighborhood.Exercise113
