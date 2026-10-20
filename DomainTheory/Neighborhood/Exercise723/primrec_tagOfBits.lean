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
import DomainTheory.Neighborhood.Exercise723.primrec_tagCode


namespace DomainTheory.Neighborhood.Exercise723

open DomainTheory.Neighborhood Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.Neighborhood.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.Neighborhood.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)




















































theorem primrec_tagOfBits : Nat.Primrec (fun t => tagOfBits t.unpair.1 t.unpair.2) := by
  have hj : Nat.Primrec (fun t : ℕ => bitsCode t.unpair.1 t.unpair.1) :=
    (primrec_bitsCode.comp (Nat.Primrec.left.pair Nat.Primrec.left)).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  exact (primrec_tagCode.comp (hj.pair Nat.Primrec.right)).of_eq fun t => by
    simp only [unpair_pair_fst, unpair_pair_snd]
    rfl

end DomainTheory.Neighborhood.Exercise723
