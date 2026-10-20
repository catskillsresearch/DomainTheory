/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Example78
public import DomainTheory.Neighborhood.Theorem74
public import DomainTheory.Neighborhood.Theorem75
public import DomainTheory.Neighborhood.Exercise514
public import DomainTheory.Neighborhood.Exercise723.Basic

@[expose] public section


namespace DomainTheory.Neighborhood.Exercise723

open DomainTheory.Neighborhood Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.Neighborhood.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.Neighborhood.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)



















































/-- **The canonical witness list for `Eⱼ = (nbhd j)ᶜ`.** `decodeList (bitsCode j j)` has exactly the
set bits of `j` as entries (order immaterial for `entries`, but fixed here for `tag`'s coding). -/
theorem mem_bitsCodeList {n k : ℕ} : k ∈ decodeList (bitsCode n n) ↔ n.testBit k = true := by
  rw [mem_decodeList_bitsCode]
  exact ⟨fun h => h.2, fun h => ⟨lt_of_testBit_true h, h⟩⟩

end DomainTheory.Neighborhood.Exercise723
