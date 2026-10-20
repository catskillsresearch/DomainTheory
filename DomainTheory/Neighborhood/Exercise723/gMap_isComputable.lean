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
public import DomainTheory.Neighborhood.Exercise723.gMap_rel_iff
public import DomainTheory.Neighborhood.Exercise723.testBit_imp_mem_Fun_isComputable
public import DomainTheory.Neighborhood.Exercise723.compl_nbhd_subset_Fun_iff

@[expose] public section


namespace DomainTheory.Neighborhood.Exercise723

open DomainTheory.Neighborhood Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.Neighborhood.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.Neighborhood.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)



































































/-- **`gMap` is computable.** The neighbourhood relation `gMap_rel_iff` reduces (via
`compl_nbhd_subset_Fun_iff`) to a bounded `∀j < k`, primitive recursive by
`testBit_imp_mem_Fun_isComputable`/`RecDecidable.bForall`. -/
theorem gMap_isComputable :
    IsComputableMap (prodPresentation PNpres PNpres) PNpres gMap := by
  have hall : RecDecidable (fun u : ℕ => ∀ j, j < u.unpair.2 →
      u.unpair.2.testBit j = true →
        j ∈ Fun (nbhd u.unpair.1.unpair.1)ᶜ (nbhd u.unpair.1.unpair.2)ᶜ) :=
    RecDecidable.of_iff (fun u => by simp only [unpair_pair_fst, unpair_pair_snd])
      (testBit_imp_mem_Fun_isComputable.bForall Nat.Primrec.right)
  refine (RecDecidable.of_iff (fun t => ?_) hall).re
  simp only [prodPresentation_X]
  exact (gMap_rel_iff _ _ _).trans (compl_nbhd_subset_Fun_iff _ _ _)

end DomainTheory.Neighborhood.Exercise723
