/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Example78
import DomainTheory.Neighborhood.Theorem74
import DomainTheory.Neighborhood.Theorem75
import DomainTheory.Neighborhood.Exercise514
import DomainTheory.Neighborhood.Exercise723.Basic
import DomainTheory.Neighborhood.Exercise723.untagRef_zero_case
import DomainTheory.Neighborhood.Exercise723.untagRef_succ_case


namespace DomainTheory.Neighborhood.Exercise723

open DomainTheory.Neighborhood Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.Neighborhood.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.Neighborhood.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)



























































/-- **`untagRef` is a genuine right-inverse of `tag`.** Strong induction on `c`, mirroring
`tag_surjective`. -/
theorem tag_untagRef (c : ℕ) : tag (untagRef c).1 (untagRef c).2 = c := by
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    rcases hc : (unnum c).1 with a | k
    · rw [untagRef_zero_case hc]
      have heq := numP_unnum c
      simp only [numP, hc] at heq
      rw [tag_nil]
      exact heq
    · rw [untagRef_succ_case hc]
      have heq : num (k + 1) (unnum c).2 = c := by
        have h := numP_unnum c
        simpa [numP, hc] using h
      have hlt : (unnum c).2 < c := by
        have hb := num_succ_left_gt k (unnum c).2
        omega
      rw [tag_cons, ih (unnum c).2 hlt, heq]

end DomainTheory.Neighborhood.Exercise723
