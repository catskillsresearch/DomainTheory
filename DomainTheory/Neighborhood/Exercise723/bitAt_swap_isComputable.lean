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


namespace DomainTheory.Neighborhood.Exercise723

open DomainTheory.Neighborhood Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.Neighborhood.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.Neighborhood.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)



































































/-- `(i,m) ↦ bitAt m i = 1`, i.e. `m.testBit i`, as a `RecDecidable₂` relation (argument order
swapped from `bitAt`'s own `(n,k) ↦ bitAt n k`, to feed `RecDecidable₂.bForallList`). -/
theorem bitAt_swap_isComputable : RecDecidable₂ (fun i m => bitAt m i = 1) :=
  ⟨fun t => bitAt t.unpair.2 t.unpair.1,
    (primrec_bitAt.comp (Nat.Primrec.right.pair Nat.Primrec.left)).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd],
    fun _ => Iff.rfl⟩

end DomainTheory.Neighborhood.Exercise723
