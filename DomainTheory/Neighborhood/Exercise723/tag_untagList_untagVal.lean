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
import DomainTheory.Neighborhood.Exercise723.tag_untagRef
import DomainTheory.Neighborhood.Exercise723.decodeList_untagList
import DomainTheory.Neighborhood.Exercise723.untagVal_spec


namespace DomainTheory.Neighborhood.Exercise723

open DomainTheory.Neighborhood Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.Neighborhood.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.Neighborhood.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)

































































/-- **`untagList`/`untagVal` genuinely decode `tag`.** -/
theorem tag_untagList_untagVal (c : ℕ) : tag (decodeList (untagList c)) (untagVal c) = c := by
  rw [decodeList_untagList, untagVal_spec]; exact tag_untagRef c

end DomainTheory.Neighborhood.Exercise723
