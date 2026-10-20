/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise118
import DomainTheory.Neighborhood.Theorem41
import DomainTheory.Neighborhood.Exercise413.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem

variable {α : Type*} {V : NeighborhoodSystem α}

namespace NeighborhoodSystem







/-- **Exercise 4.13(4) (Scott 1981, PRG-19).** Specializing 4.13(3) to the structured set
`⟨ℕ, 0, ⁺⟩`: the *unique* function `s` with `s(0) = 0` and `s(n⁺) = (s n)⁺` is the identity. This
is the iteration `n ↦ fⁿ` underlying Theorem 4.1, now justified without circularity. -/
theorem nat_iterate_unique {s : ℕ → ℕ} (h0 : s 0 = 0) (hsucc : ∀ n, s (n + 1) = s n + 1) :
    ∀ n, s n = n := by
  intro n
  induction n with
  | zero => exact h0
  | succ k ih => rw [hsucc k, ih]

end NeighborhoodSystem
end DomainTheory.Neighborhood
