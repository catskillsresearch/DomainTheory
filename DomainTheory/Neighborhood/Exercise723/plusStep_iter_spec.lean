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
import DomainTheory.Neighborhood.Exercise723.plusStep_unpair11
import DomainTheory.Neighborhood.Exercise723.plusStep_unpair12
import DomainTheory.Neighborhood.Exercise723.plusStep_unpair21
import DomainTheory.Neighborhood.Exercise723.plusStep_unpair22


namespace DomainTheory.Neighborhood.Exercise723

open DomainTheory.Neighborhood Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.Neighborhood.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.Neighborhood.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)


























theorem plusStep_iter_spec (n m : ℕ) (k : ℕ) :
    (plusStep^[k] (Nat.pair (Nat.pair n m) (Nat.pair 0 0))).unpair.1.unpair.1 = n ∧
    (plusStep^[k] (Nat.pair (Nat.pair n m) (Nat.pair 0 0))).unpair.1.unpair.2 = m ∧
    (plusStep^[k] (Nat.pair (Nat.pair n m) (Nat.pair 0 0))).unpair.2.unpair.1 = k ∧
    (plusStep^[k] (Nat.pair (Nat.pair n m) (Nat.pair 0 0))).unpair.2.unpair.2 = orUpTo n m k := by
  induction k with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [Function.iterate_zero, id_eq, unpair_pair_fst, unpair_pair_snd, orUpTo]
  | succ k ih =>
    obtain ⟨hn, hm, ha, hacc⟩ := ih
    rw [Function.iterate_succ_apply']
    set s := plusStep^[k] (Nat.pair (Nat.pair n m) (Nat.pair 0 0))
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [plusStep_unpair11, hn]
    · rw [plusStep_unpair12, hm]
    · rw [plusStep_unpair21, ha]
    · rw [plusStep_unpair22, hn, hm, ha, hacc]; rfl

end DomainTheory.Neighborhood.Exercise723
