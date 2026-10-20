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
public import DomainTheory.Neighborhood.Exercise723.mem_compl_nbhd

@[expose] public section


namespace DomainTheory.Neighborhood.Exercise723

open DomainTheory.Neighborhood Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.Neighborhood.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.Neighborhood.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)



























/-- **Choice-free converse of `compl_subset_compl_of_subset`, specialized to `nbhd`.** For cofinite
neighbourhoods the excluded sets have decidable membership (`Nat.testBit`), so unlike the general
`Set.compl_subset_compl` this direction needs only a case split on a `Bool`, not excluded middle. -/
theorem nbhd_subset_iff_compl_subset_compl (a b : ℕ) :
    nbhd a ⊆ nbhd b ↔ (nbhd b)ᶜ ⊆ (nbhd a)ᶜ := by
  constructor
  · exact compl_subset_compl_of_subset
  · intro h x hxa
    rw [mem_nbhd] at hxa ⊢
    cases hbit : b.testBit x with
    | false => rfl
    | true => exact absurd (mem_compl_nbhd.mp (h (mem_compl_nbhd.mpr hbit))) (by rw [hxa]; decide)

end DomainTheory.Neighborhood.Exercise723
