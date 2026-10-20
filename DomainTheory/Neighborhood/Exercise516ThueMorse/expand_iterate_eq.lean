/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise516
import Mathlib.Data.Nat.Bits
import DomainTheory.Neighborhood.Exercise516ThueMorse.Basic
import DomainTheory.Neighborhood.Exercise516ThueMorse.expand_tmList


namespace DomainTheory.Neighborhood.Exercise516

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419













/-- **The bridge.** The `k`-fold morphism iterate of `[0]` is the Thue–Morse parity prefix of length
`2ᵏ`: `expandᵏ[0] = tmList (2ᵏ)`. -/
theorem expand_iterate_eq (k : ℕ) : (expand^[k] [false] : Str) = tmList (2 ^ k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, expand_tmList, show 2 * 2 ^ k = 2 ^ (k + 1) by ring]

end DomainTheory.Neighborhood.Exercise516
