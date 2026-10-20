/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise414
import Mathlib.Tactic
import DomainTheory.Neighborhood.Exercise421.Basic
import DomainTheory.Neighborhood.Exercise421.upSet_zero
import DomainTheory.Neighborhood.Exercise421.upSet_succ


namespace DomainTheory.Neighborhood.Exercise421

open DomainTheory.Neighborhood.Exercise414







/-- **Exercise 4.21 / 4.13(3) (Scott 1981, PRG-19).** `[·] = upSet` is the *unique* function with
`[0] = ℕ` and `[m⁺] = [m]⁺`. -/
theorem upSet_unique (s : ℕ → Set ℕ) (h0 : s 0 = Set.univ)
    (hsucc : ∀ m, s (m + 1) = succImage (s m)) : s = upSet := by
  funext m
  induction m with
  | zero => rw [h0, upSet_zero]
  | succ k ih => rw [hsucc k, ih, upSet_succ]

end DomainTheory.Neighborhood.Exercise421
