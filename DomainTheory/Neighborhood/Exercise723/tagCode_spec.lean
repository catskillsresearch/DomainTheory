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
import DomainTheory.Neighborhood.Exercise723.tag_eq_foldl_reverse


namespace DomainTheory.Neighborhood.Exercise723

open DomainTheory.Neighborhood Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.Neighborhood.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.Neighborhood.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)



















































theorem tagCode_spec (code m : ℕ) : tagCode code m = tag (decodeList code) m := by
  unfold tagCode
  rw [foldCode_eq']
  have hstep : (fun acc x => tagStep (Nat.pair x (Nat.pair acc 0)))
      = (fun acc x => num (x + 1) acc) := by
    funext acc x
    show tagStep (Nat.pair x (Nat.pair acc 0)) = num (x + 1) acc
    unfold tagStep
    simp only [unpair_pair_fst, unpair_pair_snd]
  rw [hstep, decodeList_appendCode, decodeList_zero, List.append_nil]
  exact (tag_eq_foldl_reverse (decodeList code) m).symm

end DomainTheory.Neighborhood.Exercise723
