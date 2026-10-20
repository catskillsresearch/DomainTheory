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
public import DomainTheory.Neighborhood.Exercise723.mem_bitsCodeList
public import DomainTheory.Neighborhood.Exercise723.tag_untagList_untagVal

@[expose] public section


namespace DomainTheory.Neighborhood.Exercise723

open DomainTheory.Neighborhood Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.Neighborhood.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.Neighborhood.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)


































































/-- **`Fun` membership, decoded.** `Fun`'s defining existential over lists reduces to a bounded
existential over the finite excluded set `Eₙ`: given `c ∈ Eₙ`, `tag`'s injectivity forces the
witness list `ns` to be *exactly* `decodeList (untagList c)`, so testing `(∀n∈ns, n∈Eₘ) ∧ tag ns j
∈ Eₙ` reduces to testing `c` itself against `untagVal`/`untagList`. -/
theorem mem_Fun_compl_nbhd_iff (n m j : ℕ) :
    j ∈ Fun (nbhd n)ᶜ (nbhd m)ᶜ ↔
      ∃ c ∈ decodeList (bitsCode n n), untagVal c = j ∧
        ∀ i ∈ decodeList (untagList c), i ∈ (nbhd m)ᶜ := by
  constructor
  · rintro ⟨ns, hns, htag⟩
    have hc : tag ns j ∈ decodeList (bitsCode n n) := by
      rw [mem_bitsCodeList]; exact mem_compl_nbhd.mp htag
    refine ⟨tag ns j, hc, ?_, ?_⟩
    · exact (tag_injective (tag_untagList_untagVal (tag ns j))).2
    · rw [(tag_injective (tag_untagList_untagVal (tag ns j))).1]
      exact hns
  · rintro ⟨c, hc, hval, hall⟩
    refine ⟨decodeList (untagList c), hall, ?_⟩
    rw [mem_compl_nbhd, ← hval, tag_untagList_untagVal]
    exact mem_bitsCodeList.mp hc

end DomainTheory.Neighborhood.Exercise723
