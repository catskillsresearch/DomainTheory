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
import DomainTheory.Neighborhood.Exercise723.primrec_untagList
import DomainTheory.Neighborhood.Exercise723.bitAt_swap_isComputable


namespace DomainTheory.Neighborhood.Exercise723

open DomainTheory.Neighborhood Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.Neighborhood.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.Neighborhood.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)



































































/-- **The innermost list-check is recursively decidable.** Reindexes `bForallList` along
`untagList` to get `∀i ∈ decodeList (untagList c), bitAt m i = 1` as a function of `(c,m)`, packed
`(c,(j,m))`-style (`j` is a dummy free parameter here, along for the ride to match `gMap`'s later
packing). -/
theorem untagList_bitAt_isComputable :
    RecDecidable (fun w : ℕ => ∀ i ∈ decodeList (untagList w.unpair.1), bitAt w.unpair.2.unpair.2 i = 1) :=
  RecDecidable.of_iff (fun w => by simp only [unpair_pair_fst, unpair_pair_snd])
    (bitAt_swap_isComputable.bForallList.comp
      ((primrec_untagList.comp Nat.Primrec.left).pair (Nat.Primrec.right.comp Nat.Primrec.right)))

end DomainTheory.Neighborhood.Exercise723
