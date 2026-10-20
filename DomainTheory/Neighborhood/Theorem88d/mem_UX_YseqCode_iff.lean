/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem88b
import DomainTheory.Neighborhood.RecursiveCross
import DomainTheory.Neighborhood.Theorem88d.Basic
import DomainTheory.Neighborhood.Theorem88d.yFold_mem_iff
import DomainTheory.Neighborhood.Theorem88d.yFold_two_pow_found


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)






variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)
























































/-- **The closed-form membership characterization of `YseqCode`** — the "Set-level closed form"
this part exists to supply: a point lies in `UX (YseqCode P n)` iff it lies in some genuine
(non-junk) depth-`(n+1)` atom with bit `n` forced `1`. -/
theorem mem_UX_YseqCode_iff (n : ℕ) (z : ℚ) :
    z ∈ UX (YseqCode P n) ↔
      ∃ i < 2 ^ n, atomUEmpty P (n + 1) (i + 2 ^ n) = 0 ∧ z ∈ UX (atomUCode P (n + 1) (i + 2 ^ n)) :=
  yFold_mem_iff P n (2 ^ n) (yFold_two_pow_found P n) z

end DomainTheory.Neighborhood
