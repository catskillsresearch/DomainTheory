/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise516ThueMorse
import DomainTheory.Neighborhood.Exercise516Overlap.Basic
import DomainTheory.Neighborhood.Exercise516Overlap.tm_two_mul_ne


namespace DomainTheory.Neighborhood.Exercise516

open DomainTheory.Neighborhood


/-- `tm x = tm (x+1)` forces `x` to be **odd**: equal consecutive symbols only straddle a block
boundary `(2m+1, 2m+2)`, never a block `(2m, 2m+1)`. -/
theorem odd_of_consec_eq {x : ℕ} (h : tm x = tm (x + 1)) : Odd x := by
  rcases Nat.even_or_odd x with ⟨m, hm⟩ | hodd
  · exfalso; rw [hm, ← two_mul] at h; exact tm_two_mul_ne m h
  · exact hodd

end DomainTheory.Neighborhood.Exercise516
