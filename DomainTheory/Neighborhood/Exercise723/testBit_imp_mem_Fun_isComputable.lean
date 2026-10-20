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
import DomainTheory.Neighborhood.Exercise723.mem_Fun_compl_nbhd_isComputable


namespace DomainTheory.Neighborhood.Exercise723

open DomainTheory.Neighborhood Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.Neighborhood.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.Neighborhood.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)



































































/-- **The implication guarding a single bit of `nbhd k`'s excluded set is recursively decidable,
jointly in `(j,n,m,k)`.** Packed `(j,((n,m),k))`-style. -/
theorem testBit_imp_mem_Fun_isComputable :
    RecDecidable (fun w : ℕ => w.unpair.2.unpair.2.testBit w.unpair.1 = true →
      w.unpair.1 ∈ Fun (nbhd w.unpair.2.unpair.1.unpair.1)ᶜ (nbhd w.unpair.2.unpair.1.unpair.2)ᶜ) := by
  have hktest : RecDecidable (fun w : ℕ => w.unpair.2.unpair.2.testBit w.unpair.1 = true) :=
    ⟨fun w => bitAt w.unpair.2.unpair.2 w.unpair.1,
      (primrec_bitAt.comp ((Nat.Primrec.right.comp Nat.Primrec.right).pair Nat.Primrec.left)).of_eq
        fun w => by simp only [unpair_pair_fst, unpair_pair_snd],
      fun w => (bitAt_eq_one_iff _ _).symm⟩
  have hmem2 : RecDecidable (fun w : ℕ =>
      w.unpair.1 ∈ Fun (nbhd w.unpair.2.unpair.1.unpair.1)ᶜ (nbhd w.unpair.2.unpair.1.unpair.2)ᶜ) :=
    RecDecidable.of_iff (fun w => by simp only [unpair_pair_fst, unpair_pair_snd])
      (mem_Fun_compl_nbhd_isComputable.comp
        ((Nat.Primrec.left.comp (Nat.Primrec.left.comp Nat.Primrec.right)).pair
          (Nat.Primrec.left.pair (Nat.Primrec.right.comp (Nat.Primrec.left.comp Nat.Primrec.right)))))
  refine RecDecidable.of_iff (fun w => ?_) (hktest.not.or hmem2)
  constructor
  · intro h
    rcases hktest.em w with hb | hb
    · exact Or.inr (h hb)
    · exact Or.inl hb
  · rintro (hb | hb) hbit
    · exact absurd hbit hb
    · exact hb

end DomainTheory.Neighborhood.Exercise723
