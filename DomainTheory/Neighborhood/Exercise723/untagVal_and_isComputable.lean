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
import DomainTheory.Neighborhood.Exercise723.primrec_untagVal
import DomainTheory.Neighborhood.Exercise723.untagList_bitAt_isComputable


namespace DomainTheory.Neighborhood.Exercise723

open DomainTheory.Neighborhood Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.Neighborhood.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.Neighborhood.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)



































































/-- **`(c, j, m) ↦ untagVal c = j ∧ ∀i ∈ decodeList (untagList c), m.testBit i`.** Recursively
decidable, packed `(c,(j,m))`-style. -/
theorem untagVal_and_isComputable :
    RecDecidable (fun w : ℕ => untagVal w.unpair.1 = w.unpair.2.unpair.1 ∧
      ∀ i ∈ decodeList (untagList w.unpair.1), bitAt w.unpair.2.unpair.2 i = 1) :=
  (RecDecidable.natEq (primrec_untagVal.comp Nat.Primrec.left)
    (Nat.Primrec.left.comp Nat.Primrec.right)).and untagList_bitAt_isComputable

end DomainTheory.Neighborhood.Exercise723
