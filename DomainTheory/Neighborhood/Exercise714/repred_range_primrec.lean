/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Definition72
import DomainTheory.Neighborhood.Exercise714.Basic


namespace DomainTheory.Neighborhood.Exercise714

open NeighborhoodSystem Domain.Recursive DomainTheory.Neighborhood


/-- **The range of a primitive recursive function is recursively enumerable.** The relation
`r i = n` is recursively decidable (`RecDecidable.natEq`), and `∃ i, r i = n` is its projection, so
it is r.e. by definition of `REPred`. -/
theorem repred_range_primrec {r : ℕ → ℕ} (hr : Nat.Primrec r) :
    REPred (fun n => ∃ i, r i = n) := by
  refine ⟨fun t => r t.unpair.1 = t.unpair.2,
    RecDecidable.natEq (hr.comp Nat.Primrec.left) Nat.Primrec.right, fun n => ?_⟩
  refine exists_congr (fun i => ?_)
  simp only [unpair_pair_fst, unpair_pair_snd]

end DomainTheory.Neighborhood.Exercise714
