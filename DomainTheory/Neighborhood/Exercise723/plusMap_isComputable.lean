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
import DomainTheory.Neighborhood.Exercise723.primrec_plusIdx
import DomainTheory.Neighborhood.Exercise723.plusMap_rel_iff


namespace DomainTheory.Neighborhood.Exercise723

open DomainTheory.Neighborhood Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.Neighborhood.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.Neighborhood.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)



























/-- **`λx,y. x+y` is computable.** Reduces to `PNpres.incl_computable` against the primitive
recursive reindexing `plusIdx`. -/
theorem plusMap_isComputable :
    IsComputableMap (prodPresentation PNpres PNpres) PNpres plusMap := by
  have hincl : RecDecidable (fun s => nbhd s.unpair.1 ⊆ nbhd s.unpair.2) := PNpres.incl_computable
  have hpair : Nat.Primrec (fun t : ℕ => Nat.pair t.unpair.1.unpair.1 t.unpair.1.unpair.2) :=
    (Nat.Primrec.left.comp Nat.Primrec.left).pair (Nat.Primrec.right.comp Nat.Primrec.left)
  have hplus : Nat.Primrec (fun t : ℕ => plusIdx t.unpair.1.unpair.1 t.unpair.1.unpair.2) :=
    (primrec_plusIdx.comp hpair).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have hr : Nat.Primrec (fun t => Nat.pair (plusIdx t.unpair.1.unpair.1 t.unpair.1.unpair.2)
      t.unpair.2) := hplus.pair Nat.Primrec.right
  refine (RecDecidable.of_iff (fun t => ?_) (hincl.comp hr)).re
  simp only [prodPresentation_X, unpair_pair_fst, unpair_pair_snd]
  exact plusMap_rel_iff t.unpair.1.unpair.1 t.unpair.1.unpair.2 t.unpair.2

end DomainTheory.Neighborhood.Exercise723
