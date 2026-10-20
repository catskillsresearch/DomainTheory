/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise516
import Mathlib.Data.Nat.Bits
import DomainTheory.Neighborhood.Exercise516ThueMorse.Basic
import DomainTheory.Neighborhood.Exercise516ThueMorse.expand_append
import DomainTheory.Neighborhood.Exercise516ThueMorse.tm_two_mul
import DomainTheory.Neighborhood.Exercise516ThueMorse.tm_two_mul_add_one
import DomainTheory.Neighborhood.Exercise516ThueMorse.tmList_succ


namespace DomainTheory.Neighborhood.Exercise516

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419













/-- **The morphism step on prefixes.** `expand (tmList m) = tmList (2m)`: applying the Thue–Morse
morphism to a length-`m` prefix yields the length-`2m` prefix — this is exactly the even/odd parity
recurrence in disguise. -/
theorem expand_tmList (m : ℕ) : expand (tmList m) = tmList (2 * m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have key : tmList (2 * (m + 1)) = tmList (2 * m) ++ [tm m, !tm m] := by
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, tmList_succ, tmList_succ,
        tm_two_mul_add_one, tm_two_mul, List.append_assoc]
      rfl
    rw [tmList_succ, expand_append, ih, key, expand_cons, expand_nil]

end DomainTheory.Neighborhood.Exercise516
